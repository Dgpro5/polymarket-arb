use alloy::providers::ProviderBuilder;
use alloy::signers::Signer as _;
use alloy::signers::local::LocalSigner;
use anyhow::{Context, Error, Result, anyhow};
use base64::{Engine, engine::general_purpose::URL_SAFE as BASE64};
use ethers::prelude::*;
use ethers::signers::{LocalWallet, Signer};
use futures_util::{SinkExt, StreamExt};
use hmac::{Hmac, Mac};
use polymarket_client_sdk::POLYGON;
use polymarket_client_sdk::ctf::{Client as CtfClient, types::RedeemPositionsRequest};
use polymarket_client_sdk::types::{Address as AlloyAddress, B256, U256 as AlloyU256};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use sha2::Sha256;
use std::collections::HashMap;
use std::env;
use std::fmt;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::str::FromStr;
use std::sync::{
    Arc,
    atomic::{AtomicI64, Ordering},
};
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tokio::sync::Mutex;
use tokio_tungstenite::connect_async;
use tokio_tungstenite::tungstenite::Message;

const GAMMA_API: &str = "https://gamma-api.polymarket.com";
const CLOB_API: &str = "https://clob.polymarket.com";
const CLOB_WS_URL: &str = "wss://ws-subscriptions-clob.polymarket.com/ws/market";
const CANDLE_MS: i64 = 5 * 60 * 1000;
const DATA_DIR: &str = "data";
const LATEST_PATH: &str = "data/btc_updown_5m_latest.json";
const CSV_PATH: &str = "data/btc_updown_5m_candles.csv";
const REDEMPTIONS_PATH: &str = "data/pending_redemptions.json";
const DISCORD_WEBHOOK_URL: &str = "https://discord.com/api/webhooks/1473284259363164211/4sgTuuoGlwS4OyJ5x6-QmpPA_Q1gvsIZB9EZrb9zWX6qyA0LMQklz3IupBfINPVnpsMZ";
const ERROR_DISCORD_WEBHOOK_URL: &str = "https://discord.com/api/webhooks/1475092817654055084/_mr0tTCdzyyoJtTBwNqE6KYj6SQ0XEegZFv4j5PejJ0vq2i1Vlt0oi7IFmeAt12j0TQW";
const DETECTION_COOLDOWN_MS: i64 = 5_000; // 5 seconds — prevent rapid sequential trades
/// Stop looking for arb opportunities this many seconds before the window closes.
/// Near the close, the order book drains and Polymarket rejects one or both legs,
/// resulting in the "REST book asks sum >= 100c" stale-signal error.
const WINDOW_CLOSE_CUTOFF_SECS: i64 = 30;

const PRIVATE_KEY_ENV: &str = "PRIVATE_KEY";

// Trading parameters
// Profit threshold is computed dynamically from the live fee rate.
// Formula: sum_cents < 100.0 / (1.0 + fee_bps / 10000.0)
// This constant is a hard fallback only used if the fee fetch fails.
const MIN_PROFIT_THRESHOLD_FALLBACK: f64 = 90.0;
// Sell-back uses progressive slippage: 3% → 8% → 15% across retries (see sell_back_shares).

static LAST_DETECTION_MS: AtomicI64 = AtomicI64::new(0);
/// Global trade lock — prevents a second trade from starting while one is in flight.
/// `false` = idle, `true` = trade in progress.
static TRADE_IN_PROGRESS: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

#[derive(Debug, Clone)]
struct Candle {
    start_ms: i64,
    end_ms: i64,
    high: f64,
    low: f64,
    last_price: f64,
    /// Best ask from the WebSocket — the actual price we'd pay for a BUY.
    last_ask: f64,
    last_update_ms: i64,
}

impl Candle {
    fn new(start_ms: i64, price: f64, ask: f64, ts: i64) -> Self {
        Self {
            start_ms,
            end_ms: start_ms + CANDLE_MS,
            high: price,
            low: price,
            last_price: price,
            last_ask: ask,
            last_update_ms: ts,
        }
    }

    fn update(&mut self, price: f64, ask: f64, ts: i64) {
        if price > self.high {
            self.high = price;
        }
        if price < self.low {
            self.low = price;
        }
        self.last_price = price;
        self.last_ask = ask;
        self.last_update_ms = ts;
    }
}

#[derive(Debug, Clone)]
struct MarketInfo {
    slug: String,
    end_ts: i64,
    condition_id: String,
    asset_ids: Vec<String>,
    outcomes: Vec<String>,
}

#[derive(Debug)]
struct MarketState {
    market_slug: String,
    condition_id: String,
    asset_to_outcome: HashMap<String, String>,
    candles: HashMap<String, Candle>,
    fee_bps: u64, // maker fee in basis points, fetched from /markets/fee-rate
    end_ts: i64,  // unix timestamp when this 5-minute window closes
}

struct MoneyManager {
    total_buy_positions: i64,
    total_shares_bought: i64,
    money_spent: f64,
    balance_at_window_start: f64, // snapshot for profit calculation at window close
}

/// A market where we placed orders and need to redeem after resolution.
/// Persisted to REDEMPTIONS_PATH so redemptions survive bot restarts.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct PendingRedemption {
    slug: String,
    condition_id: String,
    /// Unix timestamp (seconds) after which we should attempt redemption.
    /// Typically window end_ts + 15 minutes (900s) to allow oracle confirmation.
    redeem_after_ts: i64,
}

/// Load pending redemptions from the JSON file, or return an empty list.
fn load_pending_redemptions() -> Vec<PendingRedemption> {
    match fs::read_to_string(REDEMPTIONS_PATH) {
        Ok(data) => serde_json::from_str(&data).unwrap_or_default(),
        Err(_) => Vec::new(),
    }
}

/// Save pending redemptions to the JSON file.
fn save_pending_redemptions(redemptions: &[PendingRedemption]) {
    if let Ok(json) = serde_json::to_string_pretty(redemptions) {
        let _ = fs::write(REDEMPTIONS_PATH, json);
    }
}

/// Add a new market to the pending redemptions file (deduplicates by condition_id).
fn add_pending_redemption(slug: &str, condition_id: &str, end_ts: i64) {
    let mut redemptions = load_pending_redemptions();
    // Don't add duplicates
    if redemptions.iter().any(|r| r.condition_id == condition_id) {
        return;
    }
    redemptions.push(PendingRedemption {
        slug: slug.to_string(),
        condition_id: condition_id.to_string(),
        redeem_after_ts: end_ts + 900, // +15 minutes for oracle confirmation
    });
    save_pending_redemptions(&redemptions);
}

#[derive(Debug, Clone)]
struct ApiCredentials {
    api_key: String,
    secret: String,
    passphrase: String,
}

#[derive(Debug, Clone)]
struct TradingWallet {
    wallet: LocalWallet,
    address: Address,
    creds: ApiCredentials,
}

#[derive(Debug, Deserialize)]
struct OrderBookLevel {
    price: String,
    size: String,
}

#[derive(Debug, Deserialize)]
struct OrderBook {
    bids: Vec<OrderBookLevel>,
    asks: Vec<OrderBookLevel>,
}

#[derive(Debug, Deserialize)]
#[allow(dead_code)]
struct BatchOrderResult {
    success: bool,
    #[serde(rename = "orderID", default)]
    order_id: String,
    #[serde(default)]
    status: String,
    #[serde(rename = "errorMsg", default)]
    error_msg: String,
    #[serde(rename = "takingAmount", default)]
    taking_amount: String,
    #[serde(rename = "makingAmount", default)]
    making_amount: String,
}

/// Response from GET /data/order/{order_hash} — used to poll fill status.
#[derive(Debug, Deserialize)]
#[allow(dead_code)]
struct OpenOrder {
    #[serde(default)]
    id: String,
    #[serde(default)]
    status: String,
    #[serde(default)]
    original_size: String,
    #[serde(default)]
    size_matched: String,
}

// Order inner object — field names and types match Polymarket's documented payload exactly
#[derive(Debug, Serialize, Clone)]
struct PolymarketOrderStruct {
    // integer, NOT a string (matches the example: "salt": 1234567890)
    salt: u64,
    maker: String,
    signer: String,
    taker: String,
    // camelCase field names as required by the API
    #[serde(rename = "tokenId")]
    token_id: String,
    #[serde(rename = "makerAmount")]
    maker_amount: String,
    #[serde(rename = "takerAmount")]
    taker_amount: String,
    // string "BUY" or "SELL", not 0/1
    side: String,
    expiration: String,
    nonce: String,
    #[serde(rename = "feeRateBps")]
    fee_rate_bps: String,
    signature: String,
    #[serde(rename = "signatureType")]
    signature_type: u8, // 0 = EOA
}

// SimpleSwap exchange object returned by POST /v3/exchanges
#[derive(Debug, Deserialize)]
#[allow(dead_code)]
struct SimpleSwapExchange {
    #[serde(rename = "publicId")]
    public_id: String,
    /// Address you must send the source currency to — do NOT hardcode this
    #[serde(rename = "addressFrom")]
    address_from: String,
    #[serde(rename = "amountFrom")]
    amount_from: String,
    status: String,
}

// Wrapper sent to POST /order
#[derive(Debug, Serialize)]
struct CreateOrderRequest {
    order: PolymarketOrderStruct,
    owner: String, // apiKey
    #[serde(rename = "orderType")]
    order_type: String, // "GTC"
    #[serde(rename = "deferExec")]
    defer_exec: bool, // false = execute immediately
}

// USDC.e (bridged USDC) on Polygon — used by Polymarket's CTF as collateral
const USDC_E_POLYGON: &str = "0x2791Bca1f2de4661ED88A30C99A7a9449Aa84174";
const ANKR_API_KEY_ENV: &str = "ANKR_API_KEY";
const SIMPLESWAP_API_KEY_ENV: &str = "SIMPLESWAP_API_KEY";

// Top up POL when balance falls below this — enough for ~50 Polygon txs
const POL_LOW_THRESHOLD: f64 = 0.5;
// Swap this many USDC.e for POL each time we top up
const POL_TOP_UP_USDC: f64 = 10.0;

// Polymarket CTF Exchange on Polygon (non-neg-risk markets)
const CTF_EXCHANGE_ADDRESS: &str = "0x4bFb41d5B3570DeFd03C39a9A4D8dE6Bd8B8982E";
// ConditionalTokens (ERC-1155) contract — holds outcome tokens.
// setApprovalForAll is required here so the CTF Exchange can transfer tokens for SELL orders.
const CONDITIONAL_TOKENS_ADDRESS: &str = "0x4D97DCd97eC945f40cF65F87097ACe5EA0476045";
const CHAIN_ID: u64 = 137;
// Zero address — any counterparty can fill the order
const ZERO_ADDRESS: &str = "0x0000000000000000000000000000000000000000";

#[tokio::main]
async fn main() -> Result<()> {
    if let Err(err) = run().await {
        let log = format!("{:#}", &err);
        eprintln!("FATAL ERROR: {log}");
        let alert = format!("FATAL ERROR:\n```\n{log}\n```");
        if let Err(alert_err) = send_error_alert(&alert).await {
            eprintln!("Failed to alert fatal error: {alert_err:#}");
        }
        return Err(err);
    }
    Ok(())
}

async fn run() -> Result<()> {
    dotenvy::dotenv().ok();
    fs::create_dir_all(DATA_DIR).context("create data dir")?;

    // Ensure the pending redemptions file exists
    if !std::path::Path::new(REDEMPTIONS_PATH).exists() {
        fs::write(REDEMPTIONS_PATH, "[]").context("create pending redemptions file")?;
    }

    // Scan all active markets for arbitrage opportunities on startup
    if let Err(e) = scan_all_markets().await {
        eprintln!("Market scan failed (non-fatal): {e:#}");
    }

    // Reads PRIVATE_KEY from the .env file (loaded above via dotenvy::dotenv()).
    // Never hardcode this value — keep it in .env and add .env to .gitignore.
    let private_key = env::var(PRIVATE_KEY_ENV).with_context(|| {
        format!("Missing env var '{PRIVATE_KEY_ENV}' — add it to your .env file")
    })?;
    if private_key.trim().is_empty() {
        return Err(anyhow!("'{PRIVATE_KEY_ENV}' is set but empty in .env"));
    }

    let client = Client::new();

    // Parse the raw wallet so we can use it for L1 auth signing
    let wallet_signer = private_key
        .trim()
        .parse::<LocalWallet>()
        .context("parse private key")?;
    let address = wallet_signer.address();
    eprintln!("Wallet: {:#x}", address);

    let creds = get_or_create_api_creds(&wallet_signer, address, &client).await?;

    let wallet = Arc::new(TradingWallet {
        wallet: wallet_signer,
        address,
        creds,
    });

    ensure_allowance(&client, &wallet, CTF_EXCHANGE_ADDRESS)
        .await
        .context("ensure USDC allowance")?;
    ensure_ctf_token_approval(&client, &wallet)
        .await
        .context("ensure ERC-1155 approval for sell orders")?;
    check_and_top_up_pol(&client, &wallet)
        .await
        .unwrap_or_else(|e| eprintln!("POL top-up check failed: {e:#}"));
    redeem_pending_markets(&private_key).await;

    // Initialize money manager
    let money: Arc<Mutex<MoneyManager>> = Arc::new(Mutex::new(MoneyManager {
        total_buy_positions: 0,
        total_shares_bought: 0,
        money_spent: 0.0,
        balance_at_window_start: 0.0,
    }));

    match get_balance(&client, &wallet.address).await {
        Ok(balance) => eprintln!("Balance: ${:.4}", balance),
        Err(e) => eprintln!("Could not fetch initial balance: {e:#}"),
    }

    let market = discover_active_btc_5m_market(&client).await?;

    // Send startup embed with market info and balance
    {
        let balance_str = match get_balance(&client, &wallet.address).await {
            Ok(b) => format!("${:.4}", b),
            Err(_) => "N/A".to_string(),
        };
        let now_utc = {
            let secs = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs();
            let h = (secs % 86400) / 3600;
            let m = (secs % 3600) / 60;
            let s = secs % 60;
            format!("{:02}:{:02}:{:02} UTC", h, m, s)
        };
        let embed = json!({
            "title": "Bot Started",
            "color": 0x3498DB,
            "fields": [
                { "name": "Market", "value": format!("[{}](https://polymarket.com/event/{})", market.slug, market.slug), "inline": false },
                { "name": "Slug", "value": &market.slug, "inline": true },
                { "name": "Time", "value": &now_utc, "inline": true },
                { "name": "Balance", "value": &balance_str, "inline": true },
                { "name": "Condition ID", "value": &market.condition_id, "inline": false }
            ],
            "footer": { "text": "Polymarket Arbitrage Bot" }
        });
        if let Err(e) = send_discord_embed(embed).await {
            eprintln!("Discord startup embed failed: {e:#}");
        }
    }

    let state = Arc::new(Mutex::new(MarketState {
        market_slug: market.slug.clone(),
        condition_id: market.condition_id.clone(),
        asset_to_outcome: market
            .asset_ids
            .iter()
            .cloned()
            .zip(market.outcomes.iter().cloned())
            .collect(),
        candles: HashMap::new(),
        fee_bps: 1000, // sensible default until first fetch
        end_ts: market.end_ts,
    }));

    // Background task: refresh fee rate every second without blocking the main loop
    let fee_task_state = Arc::clone(&state);
    let fee_task_client = client.clone();
    tokio::spawn(async move {
        let mut ticker = tokio::time::interval(Duration::from_secs(1));
        loop {
            ticker.tick().await;

            // Grab the first asset_id from the current market
            let asset_id = {
                let guard = fee_task_state.lock().await;
                guard.asset_to_outcome.keys().next().cloned()
            };

            if let Some(token_id) = asset_id {
                match get_fee_rate(&fee_task_client, &token_id).await {
                    Ok(new_fee) => {
                        let mut guard = fee_task_state.lock().await;
                        guard.fee_bps = new_fee;
                    }
                    Err(e) => {
                        // "market not found" is normal during window transitions —
                        // the old asset_id expires while we wait for the new market.
                        // Only log genuinely unexpected errors.
                        let msg = e.to_string();
                        if !msg.contains("market not found") && !msg.contains("missing base_fee") {
                            eprintln!("WARN: fee refresh failed: {e:#}");
                        }
                    }
                }
            }
        }
    });

    // Background task: refresh USDC + ERC-1155 allowances every 5 minutes.
    let allowance_task_wallet = Arc::clone(&wallet);
    let allowance_task_client = client.clone();
    tokio::spawn(async move {
        let mut ticker = tokio::time::interval(Duration::from_secs(5 * 60));
        ticker.tick().await; // first tick fires immediately, skip it
        loop {
            ticker.tick().await;
            if let Err(e) = ensure_allowance(
                &allowance_task_client,
                &*allowance_task_wallet,
                CTF_EXCHANGE_ADDRESS,
            )
            .await
            {
                eprintln!("WARN: periodic USDC allowance check failed: {e:#}");
            }
            if let Err(e) = ensure_ctf_token_approval(
                &allowance_task_client,
                &*allowance_task_wallet,
            )
            .await
            {
                eprintln!("WARN: periodic ERC-1155 approval check failed: {e:#}");
            }
        }
    });

    // Background task: write latest snapshot to disk every second
    let latest_task_state = Arc::clone(&state);
    tokio::spawn(async move {
        let mut ticker = tokio::time::interval(Duration::from_secs(1));
        loop {
            ticker.tick().await;
            let snapshot = {
                let guard = latest_task_state.lock().await;
                let mut entries = Vec::new();
                for (asset_id, candle) in guard.candles.iter() {
                    let outcome = guard
                        .asset_to_outcome
                        .get(asset_id)
                        .cloned()
                        .unwrap_or_else(|| "unknown".to_string());
                    entries.push(json!({
                        "outcome": outcome,
                        "asset_id": asset_id,
                        "window_start_ms": candle.start_ms,
                        "window_end_ms": candle.end_ms,
                        "high": candle.high,
                        "low": candle.low,
                        "last_price": candle.last_price,
                        "last_update_ms": candle.last_update_ms,
                    }));
                }
                json!({
                    "market_slug": guard.market_slug,
                    "condition_id": guard.condition_id,
                    "updated_ms": now_ms(),
                    "outcomes": entries,
                })
            };
            let _ = fs::write(LATEST_PATH, snapshot.to_string());
        }
    });

    // Background task: check pending redemptions every 2 minutes
    let redeem_task_pk = private_key.clone();
    let redeem_task_client = client.clone();
    let redeem_task_wallet = Arc::clone(&wallet);
    tokio::spawn(async move {
        let mut ticker = tokio::time::interval(Duration::from_secs(120));
        ticker.tick().await; // first tick fires immediately, skip it
        loop {
            ticker.tick().await;
            let redeemed = redeem_pending_markets(&redeem_task_pk).await;
            if redeemed > 0 {
                if let Ok(bal) = get_balance(&redeem_task_client, &redeem_task_wallet.address).await
                {
                    let embed = json!({
                        "title": "Positions Redeemed",
                        "color": 0x2ECC71,
                        "fields": [
                            { "name": "Markets Redeemed", "value": format!("{}", redeemed), "inline": true },
                            { "name": "Balance", "value": format!("${:.4}", bal), "inline": true }
                        ],
                        "footer": { "text": "Polymarket Arbitrage Bot" }
                    });
                    if let Err(e) = send_discord_embed(embed).await {
                        eprintln!("Discord redeem embed failed: {e:#}");
                    }
                }
            }
        }
    });

    let mut backoff = 2u64;
    loop {
        match discover_active_btc_5m_market(&client).await {
            Ok(new_market) => {
                let now_secs = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap_or_default()
                    .as_secs() as i64;
                let secs_remaining = (new_market.end_ts - now_secs).max(1) as u64;

                {
                    let mut guard = state.lock().await;
                    guard.market_slug = new_market.slug.clone();
                    guard.condition_id = new_market.condition_id.clone();
                    guard.asset_to_outcome = new_market
                        .asset_ids
                        .iter()
                        .cloned()
                        .zip(new_market.outcomes.iter().cloned())
                        .collect();
                    guard.candles.clear();
                    guard.fee_bps = 1000; // reset to safe default until live fetch completes
                    guard.end_ts = new_market.end_ts;
                }

                // Snapshot balance for profit tracking at window close
                match get_balance(&client, &wallet.address).await {
                    Ok(balance) => {
                        let mut m = money.lock().await;
                        m.money_spent = 0.0;
                        m.balance_at_window_start = balance;
                    }
                    Err(e) => {
                        eprintln!("WARN: Could not fetch balance: {e:#}");
                    }
                }

                // Fetch live fee rate for this market and store it in state.
                // Uses the first asset_id — both UP and DOWN legs share the same fee.
                if let Some(first_asset) = new_market.asset_ids.first() {
                    if let Ok(fee_bps) = get_fee_rate(&client, first_asset).await {
                        state.lock().await.fee_bps = fee_bps;
                    }
                }

                let mut window_closed = false;
                let mut close_reason = "unknown";
                tokio::select! {
                    result = run_socket(
                        Arc::clone(&state),
                        Arc::clone(&money),
                        Arc::clone(&wallet),
                        &new_market.asset_ids
                    ) => {
                        match result {
                            Ok(_) => {
                                backoff = 2;
                                window_closed = true;
                                close_reason = "socket_closed";
                            }
                            Err(e) if e.to_string().contains("NO NEW ASSETS") => {
                                backoff = 2;
                                window_closed = true;
                                close_reason = "no_new_assets";
                            }
                            Err(e) => {
                                eprintln!("Socket error: {e:#}. Reconnecting in {backoff}s...");
                                tokio::time::sleep(Duration::from_secs(backoff)).await;
                                backoff = (backoff * 2).min(60);
                            }
                        }
                    }
                    _ = tokio::time::sleep(Duration::from_secs(secs_remaining)) => {
                        tokio::time::sleep(Duration::from_secs(3)).await;
                        backoff = 2;
                        window_closed = true;
                        close_reason = "timer";
                    }
                }

                if window_closed {
                    let slug_closing = {
                        let guard = state.lock().await;
                        guard.market_slug.clone()
                    };

                    // Window-close embed — show what we spent this window
                    let balance_now = get_balance(&client, &wallet.address).await.unwrap_or(0.0);
                    let pending = load_pending_redemptions();
                    let m = money.lock().await;
                    let embed = json!({
                        "title": "Window Closed",
                        "color": 0x95A5A6,
                        "fields": [
                            { "name": "Slug", "value": &slug_closing, "inline": false },
                            { "name": "Close Reason", "value": close_reason, "inline": true },
                            { "name": "Balance", "value": format!("${:.4}", balance_now), "inline": true },
                            { "name": "Total Spent", "value": format!("${:.4}", m.money_spent), "inline": true },
                            { "name": "Trades", "value": format!("{}", m.total_buy_positions), "inline": true },
                            { "name": "Total Shares", "value": format!("{}", m.total_shares_bought), "inline": true },
                            { "name": "Pending Redemptions", "value": format!("{}", pending.len()), "inline": true }
                        ],
                        "footer": { "text": "Redemptions checked every 2 min by background task" }
                    });
                    drop(m);
                    if let Err(e) = send_discord_embed(embed).await {
                        eprintln!("Discord window-close embed failed: {e:#}");
                    }

                    // Opportunistic redemption check on window close (background task
                    // also checks every 2 min, but this catches any that just became ready).
                    redeem_pending_markets(&private_key).await;

                    // Refill POL if running low
                    check_and_top_up_pol(&client, &wallet)
                        .await
                        .unwrap_or_else(|e| eprintln!("WARN: POL top-up check failed: {e:#}"));
                }
            }
            Err(e) => {
                eprintln!("Market discovery failed: {e:#}. Retrying in {backoff}s...");
                tokio::time::sleep(Duration::from_secs(backoff)).await;
                backoff = (backoff * 2).min(10);
            }
        }
    }
}

// ── Market Scanner ────────────────────────────────────────────────────────────
//
// Fetches ALL active binary markets from Polymarket's Gamma API and checks each
// one for arbitrage opportunities by comparing CLOB order book best-ask prices.
// A market is flagged when (best_ask_outcome_1 + best_ask_outcome_2) < 100c,
// meaning you can buy both sides for less than the guaranteed $1.00 payout.

/// Scans all active Polymarket events for binary (YES/NO or UP/DOWN) arbitrage.
async fn scan_all_markets() -> Result<()> {
    eprintln!("=== Polymarket Arbitrage Scanner ===");
    eprintln!("Fetching all active events...\n");

    let client = Client::new();
    let mut offset = 0u64;
    let limit = 100u64;
    let mut total_markets = 0u64;
    let mut total_binary = 0u64;
    let mut total_no_liquidity = 0u64;
    let mut total_no_arb = 0u64;
    let mut opportunities: Vec<(String, String, f64, f64, f64, f64, f64)> = Vec::new();

    loop {
        let url = format!(
            "{GAMMA_API}/events?active=true&closed=false&limit={limit}&offset={offset}"
        );
        let resp = client.get(&url).send().await.context("fetch events page")?;
        let events: Vec<Value> = resp.json().await.context("parse events response")?;

        if events.is_empty() {
            break;
        }

        for event in &events {
            let event_title = event
                .get("title")
                .and_then(|v| v.as_str())
                .unwrap_or("(untitled)");

            let markets = match event.get("markets").and_then(|v| v.as_array()) {
                Some(m) => m,
                None => continue,
            };

            for market in markets {
                total_markets += 1;

                let question = market
                    .get("question")
                    .and_then(|v| v.as_str())
                    .unwrap_or("(no question)");
                let active = market
                    .get("active")
                    .and_then(|v| v.as_bool())
                    .unwrap_or(false);
                let closed = market
                    .get("closed")
                    .and_then(|v| v.as_bool())
                    .unwrap_or(true);

                if !active || closed {
                    continue;
                }

                // Parse outcomes and token IDs
                let outcomes = match parse_string_array(market.get("outcomes")) {
                    Ok(o) => o,
                    Err(_) => continue,
                };
                let token_ids = match parse_string_array(market.get("clobTokenIds")) {
                    Ok(t) => t,
                    Err(_) => continue,
                };

                // Only binary markets: YES/NO or UP/DOWN
                if outcomes.len() != 2 || token_ids.len() != 2 {
                    continue;
                }

                let o1 = outcomes[0].to_uppercase();
                let o2 = outcomes[1].to_uppercase();
                let is_binary = (o1 == "YES" && o2 == "NO")
                    || (o1 == "NO" && o2 == "YES")
                    || (o1 == "UP" && o2 == "DOWN")
                    || (o1 == "DOWN" && o2 == "UP");

                if !is_binary {
                    continue;
                }

                total_binary += 1;

                // Fetch CLOB order books for both tokens
                let (book1, book2) = tokio::join!(
                    get_order_book(&client, &token_ids[0]),
                    get_order_book(&client, &token_ids[1]),
                );

                let book1 = match book1 {
                    Ok(b) => b,
                    Err(_) => continue,
                };
                let book2 = match book2 {
                    Ok(b) => b,
                    Err(_) => continue,
                };

                let ask1: Option<f64> = book1.asks.first().and_then(|l| l.price.parse().ok());
                let ask2: Option<f64> = book2.asks.first().and_then(|l| l.price.parse().ok());
                let bid1: Option<f64> = book1.bids.first().and_then(|l| l.price.parse().ok());
                let bid2: Option<f64> = book2.bids.first().and_then(|l| l.price.parse().ok());

                // Need asks on both sides — that's what we pay with FAK
                let (a1, a2) = match (ask1, ask2) {
                    (Some(a), Some(b)) => (a, b),
                    _ => {
                        total_no_liquidity += 1;
                        continue;
                    }
                };

                let ask_sum = a1 + a2;
                let ask_sum_cents = ask_sum * 100.0;
                let bid_sum_cents = match (bid1, bid2) {
                    (Some(b1), Some(b2)) => (b1 + b2) * 100.0,
                    _ => f64::NAN,
                };

                // Get depth for display (ask-side depth — what we can buy)
                let depth1 = book1
                    .asks
                    .first()
                    .and_then(|l| l.size.parse::<f64>().ok())
                    .unwrap_or(0.0);
                let depth2 = book2
                    .asks
                    .first()
                    .and_then(|l| l.size.parse::<f64>().ok())
                    .unwrap_or(0.0);

                // Arb exists when best_ask_1 + best_ask_2 < 100c
                // (i.e. we can BUY both sides for less than the $1 payout)
                if ask_sum_cents < 100.0 {
                    let edge = 100.0 - ask_sum_cents;
                    opportunities.push((
                        event_title.to_string(),
                        question.to_string(),
                        a1 * 100.0,
                        a2 * 100.0,
                        ask_sum_cents,
                        edge,
                        depth1.min(depth2),
                    ));
                    eprintln!(
                        "  ARB FOUND: {} | ask: {:.1}c + {:.1}c = {:.1}c (edge +{:.1}c) | bid sum: {:.1}c | depth: {:.0}",
                        question,
                        a1 * 100.0,
                        a2 * 100.0,
                        ask_sum_cents,
                        edge,
                        bid_sum_cents,
                        depth1.min(depth2),
                    );
                } else {
                    total_no_arb += 1;
                    eprintln!(
                        "  NO ARB: {} | ask: {:.1}c + {:.1}c = {:.1}c | bid sum: {:.1}c",
                        question,
                        a1 * 100.0,
                        a2 * 100.0,
                        ask_sum_cents,
                        bid_sum_cents,
                    );
                }

                // Rate limit: ~5 requests per second (2 per market)
                tokio::time::sleep(Duration::from_millis(100)).await;
            }
        }

        offset += limit;
        eprintln!(
            "  ... scanned {} events so far ({} markets, {} binary)",
            offset,
            total_markets,
            total_binary,
        );
    }

    // ── Summary ──────────────────────────────────────────────────────────────
    eprintln!("\n=== Scan Complete ===");
    eprintln!(
        "Total markets: {} | Binary (YES/NO or UP/DOWN): {} | No liquidity: {} | No arb: {} | Arb found: {}",
        total_markets, total_binary, total_no_liquidity, total_no_arb, opportunities.len()
    );

    if opportunities.is_empty() {
        eprintln!("No arbitrage opportunities found.");
    } else {
        opportunities.sort_by(|a, b| b.5.partial_cmp(&a.5).unwrap_or(std::cmp::Ordering::Equal));
        eprintln!("\n{} ARBITRAGE OPPORTUNITIES:\n", opportunities.len());
        eprintln!(
            "{:<60} {:>8} {:>8} {:>8} {:>8} {:>8}",
            "Market", "Ask1(c)", "Ask2(c)", "Sum(c)", "Edge(c)", "Depth"
        );
        eprintln!("{}", "-".repeat(112));
        for (_, question, a1, a2, sum, edge, depth) in &opportunities {
            let q = if question.len() > 58 {
                format!("{}...", &question[..55])
            } else {
                question.clone()
            };
            eprintln!(
                "{:<60} {:>8.1} {:>8.1} {:>8.1} {:>+8.1} {:>8.0}",
                q, a1, a2, sum, edge, depth
            );
        }
    }

    Ok(())
}

fn compute_current_slug() -> (String, i64) {
    let now_secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs() as i64;

    let remainder = now_secs % 300;
    let start_ts = now_secs - remainder;
    let end_ts = start_ts + 300;

    (format!("btc-updown-5m-{start_ts}"), end_ts)
}

async fn discover_active_btc_5m_market(client: &Client) -> Result<MarketInfo> {
    let (slug, end_ts) = compute_current_slug();

    let url = format!("{GAMMA_API}/markets?slug={slug}");
    let resp = client
        .get(&url)
        .send()
        .await
        .context("fetch btc-updown-5m market by slug")?;

    let data: Value = resp.json().await.context("parse market response")?;

    let market = data.as_array().and_then(|arr| arr.first()).ok_or_else(|| {
        anyhow!(
            "Market not found for slug '{slug}'. \
                 It may not be listed yet — wait a few seconds and retry. \
                 Verify at: https://polymarket.com/event/{slug}"
        )
    })?;

    let mut info = parse_market_info(market)?;
    info.slug = slug;
    info.end_ts = end_ts;
    Ok(info)
}

fn parse_market_info(market: &Value) -> Result<MarketInfo> {
    let condition_id = market
        .get("conditionId")
        .and_then(|v| v.as_str())
        .ok_or_else(|| anyhow!("missing conditionId"))?
        .to_string();

    let asset_ids = parse_string_array(market.get("clobTokenIds")).context("parse clobTokenIds")?;
    let outcomes = parse_string_array(market.get("outcomes")).context("parse outcomes")?;

    if asset_ids.is_empty() || outcomes.is_empty() {
        return Err(anyhow!("empty outcomes or token ids"));
    }
    if asset_ids.len() != outcomes.len() {
        return Err(anyhow!(
            "token id count {} does not match outcomes {}",
            asset_ids.len(),
            outcomes.len()
        ));
    }

    Ok(MarketInfo {
        slug: String::new(),
        end_ts: 0,
        condition_id,
        asset_ids,
        outcomes,
    })
}

fn parse_string_array(value: Option<&Value>) -> Result<Vec<String>> {
    let Some(value) = value else {
        return Err(anyhow!("missing field"));
    };

    if let Some(arr) = value.as_array() {
        return Ok(arr
            .iter()
            .filter_map(|v| v.as_str().map(|s| s.to_string()))
            .collect());
    }

    if let Some(s) = value.as_str() {
        let parsed: Vec<String> = serde_json::from_str(s).context("parse json string array")?;
        return Ok(parsed);
    }

    Err(anyhow!("unexpected field type"))
}

async fn run_socket(
    state: Arc<Mutex<MarketState>>,
    money: Arc<Mutex<MoneyManager>>,
    wallet: Arc<TradingWallet>,
    asset_ids: &[String],
) -> Result<()> {
    let (ws_stream, _) = connect_async(CLOB_WS_URL)
        .await
        .context("connect clob ws")?;
    let (mut write, mut read) = ws_stream.split();
    let subscribe_msg = json!({
        "type": "market",
        "assets_ids": asset_ids
    })
    .to_string();
    write
        .send(Message::Text(subscribe_msg))
        .await
        .context("send subscribe")?;

    while let Some(msg) = read.next().await {
        match msg {
            Ok(Message::Text(text)) => {
                match text.as_str() {
                    "ping" => {
                        write.send(Message::Text("pong".to_string())).await.ok();
                        continue;
                    }
                    "pong" => continue,
                    "NO NEW ASSETS" => {
                        return Err(anyhow!("NO NEW ASSETS"));
                    }
                    _ => {}
                }

                if let Ok(value) = serde_json::from_str::<Value>(&text) {
                    handle_clob_message(&state, &money, &wallet, &value).await?;
                }
            }
            Ok(Message::Ping(data)) => {
                write.send(Message::Pong(data)).await.ok();
            }
            Ok(Message::Close(_)) => break,
            Ok(_) => {}
            Err(e) => {
                return Err(anyhow!("WS error: {e}"));
            }
        }
    }

    Ok(())
}

async fn handle_clob_message(
    state: &Arc<Mutex<MarketState>>,
    money: &Arc<Mutex<MoneyManager>>,
    wallet: &Arc<TradingWallet>,
    value: &Value,
) -> Result<()> {
    if let Some(arr) = value.as_array() {
        for item in arr {
            handle_clob_message_single(state, money, wallet, item).await?;
        }
        return Ok(());
    }

    if let Some(data) = value.get("data") {
        if let Some(arr) = data.as_array() {
            for item in arr {
                handle_clob_message_single(state, money, wallet, item).await?;
            }
            return Ok(());
        }
        if data.is_object() {
            return handle_clob_message_single(state, money, wallet, data).await;
        }
    }

    handle_clob_message_single(state, money, wallet, value).await
}

async fn handle_clob_message_single(
    state: &Arc<Mutex<MarketState>>,
    money: &Arc<Mutex<MoneyManager>>,
    wallet: &Arc<TradingWallet>,
    value: &Value,
) -> Result<()> {
    let Some(event_type) = value.get("event_type").and_then(|v| v.as_str()) else {
        return Ok(());
    };

    match event_type {
        "best_bid_ask" => {
            if let Some((asset_id, price, ask, ts)) = parse_best_bid_ask(value) {
                update_outcome_price(state, money, wallet, &asset_id, price, Some(ask), ts).await?;
            }
        }
        "last_trade_price" => {
            if let Some((asset_id, price, ts)) = parse_last_trade(value) {
                update_outcome_price(state, money, wallet, &asset_id, price, None, ts).await?;
            }
        }
        "book" => {
            if let Some((asset_id, price, ts)) = parse_book_mid(value) {
                update_outcome_price(state, money, wallet, &asset_id, price, None, ts).await?;
            }
        }
        "price_change" => {
            if let Some(ts) = parse_timestamp(value.get("timestamp")) {
                let root_asset = value.get("asset_id").and_then(|v| v.as_str());
                let changes = value
                    .get("price_changes")
                    .or_else(|| value.get("changes"))
                    .and_then(|v| v.as_array());
                if let Some(changes) = changes {
                    for change in changes {
                        if let Some((asset_id, price)) = parse_price_change(change, root_asset) {
                            update_outcome_price(state, money, wallet, &asset_id, price, None, ts)
                                .await?;
                        }
                    }
                }
            }
        }
        _ => {}
    }

    Ok(())
}

/// Returns (asset_id, midpoint, best_ask, timestamp).
fn parse_best_bid_ask(value: &Value) -> Option<(String, f64, f64, i64)> {
    let asset_id = value.get("asset_id")?.as_str()?.to_string();
    let best_bid = value
        .get("best_bid")
        .and_then(|v| v.as_str())
        .and_then(parse_price);
    let best_ask = value
        .get("best_ask")
        .and_then(|v| v.as_str())
        .and_then(parse_price);
    let ts = parse_timestamp(value.get("timestamp")).unwrap_or_else(now_ms);

    let price = match (best_bid, best_ask) {
        (Some(bid), Some(ask)) => (bid + ask) / 2.0,
        (Some(bid), None) => bid,
        (None, Some(ask)) => ask,
        (None, None) => return None,
    };

    // For the ask, fall back to the midpoint if no ask is available.
    let ask = best_ask.unwrap_or(price);

    Some((asset_id, price, ask, ts))
}

fn parse_last_trade(value: &Value) -> Option<(String, f64, i64)> {
    let asset_id = value.get("asset_id")?.as_str()?.to_string();
    let price = value
        .get("price")
        .and_then(|v| v.as_str())
        .and_then(parse_price)?;
    let ts = parse_timestamp(value.get("timestamp")).unwrap_or_else(now_ms);
    Some((asset_id, price, ts))
}

fn parse_book_mid(value: &Value) -> Option<(String, f64, i64)> {
    let asset_id = value.get("asset_id")?.as_str()?.to_string();
    let ts = parse_timestamp(value.get("timestamp")).unwrap_or_else(now_ms);

    let bids = value
        .get("bids")
        .or_else(|| value.get("buys"))
        .and_then(|v| v.as_array())?;
    let asks = value
        .get("asks")
        .or_else(|| value.get("sells"))
        .and_then(|v| v.as_array())?;

    let best_bid = bids
        .iter()
        .filter_map(|entry| entry.get("price").and_then(|v| v.as_str()))
        .filter_map(parse_price)
        .max_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));

    let best_ask = asks
        .iter()
        .filter_map(|entry| entry.get("price").and_then(|v| v.as_str()))
        .filter_map(parse_price)
        .min_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));

    let price = match (best_bid, best_ask) {
        (Some(bid), Some(ask)) => (bid + ask) / 2.0,
        (Some(bid), None) => bid,
        (None, Some(ask)) => ask,
        (None, None) => return None,
    };

    Some((asset_id, price, ts))
}

fn parse_price_change(change: &Value, root_asset: Option<&str>) -> Option<(String, f64)> {
    let asset_id = if let Some(id) = change.get("asset_id").and_then(|v| v.as_str()) {
        id.to_string()
    } else {
        root_asset?.to_string()
    };
    let best_bid = change
        .get("best_bid")
        .and_then(|v| v.as_str())
        .and_then(parse_price);
    let best_ask = change
        .get("best_ask")
        .and_then(|v| v.as_str())
        .and_then(parse_price);
    let fallback = change
        .get("price")
        .and_then(|v| v.as_str())
        .and_then(parse_price);

    let price = match (best_bid, best_ask) {
        (Some(bid), Some(ask)) => (bid + ask) / 2.0,
        (Some(bid), None) => bid,
        (None, Some(ask)) => ask,
        (None, None) => fallback?,
    };

    Some((asset_id, price))
}

async fn update_outcome_price(
    state: &Arc<Mutex<MarketState>>,
    money: &Arc<Mutex<MoneyManager>>,
    wallet: &Arc<TradingWallet>,
    asset_id: &str,
    price: f64,
    ask: Option<f64>,
    ts: i64,
) -> Result<()> {
    let start_ms = ts - (ts % CANDLE_MS);
    // If no ask provided (e.g. last_trade_price), use the price as fallback.
    let ask = ask.unwrap_or(price);

    let mut guard = state.lock().await;
    if !guard.asset_to_outcome.contains_key(asset_id) {
        return Ok(());
    }

    let mut finished: Option<Candle> = None;

    match guard.candles.get_mut(asset_id) {
        Some(candle) if candle.start_ms == start_ms => {
            candle.update(price, ask, ts);
        }
        Some(prev) => {
            finished = Some(prev.clone());
            guard
                .candles
                .insert(asset_id.to_string(), Candle::new(start_ms, price, ask, ts));
        }
        None => {
            guard
                .candles
                .insert(asset_id.to_string(), Candle::new(start_ms, price, ask, ts));
        }
    }

    if let Some(prev) = finished.as_ref() {
        write_candle_csv(&guard, asset_id, prev)?;
    }

    print_up_down(&guard, money, wallet).await?;
    Ok(())
}

async fn print_up_down(
    state: &MarketState,
    money: &Arc<Mutex<MoneyManager>>,
    wallet: &Arc<TradingWallet>,
) -> Result<()> {
    let mut up_id = None;
    let mut up_price = None;
    let mut up_ask = None;
    let mut down_id = None;
    let mut down_price = None;
    let mut down_ask = None;

    for (asset_id, candle) in state.candles.iter() {
        let outcome = state
            .asset_to_outcome
            .get(asset_id)
            .cloned()
            .unwrap_or_else(|| "unknown".to_string());
        if outcome.eq_ignore_ascii_case("up") {
            up_id = Some(asset_id.clone());
            up_price = Some(candle.last_price);
            up_ask = Some(candle.last_ask);
        } else if outcome.eq_ignore_ascii_case("down") {
            down_id = Some(asset_id.clone());
            down_price = Some(candle.last_price);
            down_ask = Some(candle.last_ask);
        }
    }

    if let (Some(up), Some(down), Some(up_asset), Some(down_asset)) =
        (up_price, down_price, up_id, down_id)
    {
        // Round to tick size FIRST, then check profitability.
        // Raw prices may look profitable but round up past 100 cents.
        // e.g. up=0.475 -> 0.48, down=0.525 -> 0.53 => sum=101 cents => loss.
        let up = (up * 100.0).round() / 100.0;
        let down = (down * 100.0).round() / 100.0;
        let sum_cents = (up + down) * 100.0;

        // Dynamic threshold: profitable only when sum_cents * (1 + fee) < 100
        let fee_bps = state.fee_bps;
        let profit_threshold = if fee_bps > 0 {
            100.0 / (1.0 + fee_bps as f64 / 10000.0)
        } else {
            MIN_PROFIT_THRESHOLD_FALLBACK
        };

        if sum_cents < profit_threshold {
            // ── Window-close cutoff ──────────────────────────────────
            // In the last N seconds before the window closes, the order book
            // drains and Polymarket locks one side.  Any "arb" signal here is
            // a phantom — one or both legs will be rejected.  Skip early.
            let now_secs = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs() as i64;
            let secs_left = state.end_ts - now_secs;
            if secs_left <= WINDOW_CLOSE_CUTOFF_SECS {
                return Ok(());
            }

            // ── Cooldown gate ────────────────────────────────────────
            let now = now_ms();
            let last = LAST_DETECTION_MS.load(Ordering::Relaxed);
            if now - last < DETECTION_COOLDOWN_MS {
                return Ok(());
            }

            // ── Trade lock gate ──────────────────────────────────────
            // Prevents a second trade from starting while one is in flight.
            // compare_exchange: only proceed if currently false (idle).
            if TRADE_IN_PROGRESS
                .compare_exchange(
                    false,
                    true,
                    std::sync::atomic::Ordering::SeqCst,
                    std::sync::atomic::Ordering::SeqCst,
                )
                .is_err()
            {
                eprintln!("Trade already in progress — skipping this opportunity");
                return Ok(());
            }

            LAST_DETECTION_MS.store(now, Ordering::Relaxed);

            // Ensure the lock is always released, even on early returns/panics.
            // Use WebSocket best-ask prices for orders (low latency).
            // Round to tick size, fall back to midpoint if ask unavailable.
            let up_ask_price = ((up_ask.unwrap_or(up) * 100.0).round()) / 100.0;
            let down_ask_price = ((down_ask.unwrap_or(down) * 100.0).round()) / 100.0;
            let trade_result = execute_arbitrage_trade(
                wallet,
                &up_asset,
                &down_asset,
                up,
                down,
                up_ask_price,
                down_ask_price,
                sum_cents,
                fee_bps,
            )
            .await;

            // Update cooldown AFTER trade completes so the 5s window starts from trade end.
            LAST_DETECTION_MS.store(now_ms(), Ordering::Relaxed);
            TRADE_IN_PROGRESS.store(false, Ordering::SeqCst);

            match trade_result {
                Ok((trade_result, details)) => {
                    let mut money = money.lock().await;
                    money.money_spent += trade_result.total_spent;
                    money.total_buy_positions += 1;
                    money.total_shares_bought += (trade_result.shares_bought * 2) as i64;

                    let edge = 100.0 - sum_cents;
                    let fill_note = if details.up_filled == details.requested_shares
                        && details.down_filled == details.requested_shares
                    {
                        "full".to_string()
                    } else {
                        format!(
                            "partial — UP {}/{}, DOWN {}/{}",
                            details.up_filled, details.requested_shares,
                            details.down_filled, details.requested_shares
                        )
                    };
                    let embed = json!({
                        "title": "Trade Executed (Batch FAK)",
                        "color": 0x2ECC71,
                        "fields": [
                            { "name": "UP Price", "value": format!("{:.2}c", up * 100.0), "inline": true },
                            { "name": "DOWN Price", "value": format!("{:.2}c", down * 100.0), "inline": true },
                            { "name": "Sum / Edge", "value": format!("{:.2}c / +{:.2}c", sum_cents, edge), "inline": true },
                            { "name": "Matched Shares", "value": format!("{}", trade_result.shares_bought), "inline": true },
                            { "name": "Total Spent", "value": format!("${:.4}", trade_result.total_spent), "inline": true },
                            { "name": "Fill", "value": fill_note, "inline": true },
                            { "name": "Fee (UP/DOWN)", "value": format!("{}bps / {}bps", details.up_fee_bps, details.down_fee_bps), "inline": true },
                            { "name": "Balance Before", "value": format!("${:.4}", details.balance_before), "inline": true },
                            { "name": "Balance After", "value": format!("${:.4}", details.balance_after), "inline": true },
                            { "name": "Window Trades", "value": format!("{}", money.total_buy_positions), "inline": true },
                            { "name": "UP Order", "value": format!("`{}` ({})", details.up_order_id, details.up_status), "inline": false },
                            { "name": "DOWN Order", "value": format!("`{}` ({})", details.down_order_id, details.down_status), "inline": false },
                            { "name": "Book Depth (UP/DOWN)", "value": format!("{:.0} / {:.0}", details.up_depth, details.down_depth), "inline": true },
                            { "name": "UP Asset", "value": format!("`{}`", up_asset), "inline": false },
                            { "name": "DOWN Asset", "value": format!("`{}`", down_asset), "inline": false }
                        ],
                        "footer": { "text": format!("{}", state.market_slug) }
                    });
                    if let Err(e) = send_discord_embed(embed).await {
                        eprintln!("Discord embed failed: {e:#}");
                    }

                    // Record this market for later redemption
                    add_pending_redemption(
                        &state.market_slug,
                        &state.condition_id,
                        state.end_ts,
                    );
                }
                Err(e) => {
                    let log = format!("{:#}", e);
                    eprintln!("TRADE FAILED: {log}");
                    // Only send Discord alerts for unexpected errors, not stale-signal
                    // "no arb" rejections (REST book sum >= 100c) or insufficient balance.
                    if !is_insufficient_balance_error(&e) && !is_stale_signal_error(&e) {
                        let alert = format!(
                            "Trade failed (assets {}/{} | sum {:.2}c):\n```\n{}\n```",
                            up_asset, down_asset, sum_cents, log
                        );
                        if let Err(alert_err) = send_error_alert(&alert).await {
                            eprintln!("Failed to send trade failure alert: {alert_err:#}");
                        }
                    }
                }
            }
        }
    }

    Ok(())
}

const MIN_BALANCE_USDC: f64 = 5.0;

#[derive(Debug)]
struct InsufficientBalanceError {
    balance: f64,
    required: f64,
}

impl fmt::Display for InsufficientBalanceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Balance ${:.2} < ${:.2} minimum",
            self.balance, self.required
        )
    }
}

impl std::error::Error for InsufficientBalanceError {}

fn is_insufficient_balance_error(err: &Error) -> bool {
    err.downcast_ref::<InsufficientBalanceError>().is_some()
}

/// Stale-signal errors (REST book >= 100c, no liquidity, too few shares) are
/// informational, not actionable. Suppress their Discord alerts.
fn is_stale_signal_error(err: &Error) -> bool {
    let msg = format!("{err:#}");
    msg.contains("WS signal is stale")
        || msg.contains("No ask liquidity on REST book")
        || msg.contains("shares possible (min")
}

#[derive(Debug)]
struct TradeResult {
    shares_bought: u64,
    total_spent: f64,
}

/// Detailed info returned alongside TradeResult so the caller can build
/// a rich Discord embed without re-fetching anything.
struct TradeDetails {
    balance_before: f64,
    balance_after: f64,
    up_order_id: String,
    up_status: String,
    down_order_id: String,
    down_status: String,
    up_fee_bps: u64,
    down_fee_bps: u64,
    up_depth: f64,
    down_depth: f64,
    requested_shares: u64,
    up_filled: u64,
    down_filled: u64,
}

/// Determine how many shares a FAK order actually filled.
/// Polls the order status endpoint (with retries) for the exact fill size.
/// Falls back to computing from `takingAmount` if the poll doesn't return data.
/// NEVER blindly returns `requested_shares` — FAK fills can exceed or undershoot
/// the requested amount depending on market price vs limit price.
async fn determine_fill_shares(
    client: &Client,
    wallet: &Arc<TradingWallet>,
    res: &BatchOrderResult,
    requested_shares: u64,
    order_price: f64,
) -> u64 {
    if !res.success {
        return 0;
    }

    // If status is empty AND no order ID, the FAK matched nothing.
    if res.status.is_empty() && res.order_id.is_empty() {
        return 0;
    }

    // ── Try 1: Use takingAmount from batch response (shares received) ───
    // takingAmount is the number of conditional tokens received (= shares for BUY).
    if !res.taking_amount.is_empty() {
        if let Ok(taking) = res.taking_amount.parse::<f64>() {
            if taking > 0.0 {
                let shares = taking.round() as u64;
                eprintln!(
                    "  fill source: takingAmount={} → {} shares (requested {})",
                    res.taking_amount, shares, requested_shares
                );
                return shares;
            }
        }
    }

    // ── Try 2: Poll order status endpoint for size_matched (with retries) ───
    if !res.order_id.is_empty() {
        for poll_attempt in 0..3u32 {
            if poll_attempt > 0 {
                tokio::time::sleep(Duration::from_millis(500)).await;
            }
            if let Ok(status) = get_order_status(client, wallet, &res.order_id).await {
                eprintln!(
                    "  poll {}: status={} size_matched={} original_size={}",
                    poll_attempt + 1, status.status, status.size_matched, status.original_size
                );
                if let Ok(matched) = status.size_matched.parse::<f64>() {
                    if matched > 0.0 {
                        let shares = matched.round() as u64;
                        return shares;
                    }
                }
            }
        }
    }

    // ── Try 3: Compute from makingAmount (USDC spent) / order_price ────
    // makingAmount is USDC spent; shares ≈ makingAmount / price_per_share.
    if !res.making_amount.is_empty() && order_price > 0.0 {
        if let Ok(making) = res.making_amount.parse::<f64>() {
            if making > 0.0 {
                let shares = (making / order_price).round() as u64;
                eprintln!(
                    "  fill source: makingAmount={} / price={:.4} → {} shares (requested {})",
                    res.making_amount, order_price, shares, requested_shares
                );
                return shares;
            }
        }
    }

    // ── Last resort: status says MATCHED but we have no amount data ────
    // Log a warning — this path should rarely trigger now that we have retries.
    if res.status.eq_ignore_ascii_case("MATCHED") {
        eprintln!(
            "  WARNING: status=MATCHED but no fill data available. Falling back to requested_shares={}. \
             This may be inaccurate if market price differs from limit price.",
            requested_shares
        );
        return requested_shares;
    }

    0
}

/// Places UP and DOWN orders simultaneously via batch FAK submission.
/// Both orders are pre-built and signed, then submitted in a single HTTP
/// request to minimize the timing gap.  FAK allows partial fills — any
/// mismatch between legs is resolved by selling back the excess.
async fn execute_arbitrage_trade(
    wallet: &Arc<TradingWallet>,
    up_asset_id: &str,
    down_asset_id: &str,
    _up_price: f64,
    _down_price: f64,
    up_ask: f64,
    down_ask: f64,
    _sum_cents: f64,
    fee_bps: u64,
) -> Result<(TradeResult, TradeDetails)> {
    let client = Client::new();

    // ── Check balance ────────────────────────────────────────────────────
    let balance = get_balance(&client, &wallet.address)
        .await
        .context("balance check before trade")?;
    if balance < MIN_BALANCE_USDC {
        return Err(InsufficientBalanceError {
            balance,
            required: MIN_BALANCE_USDC,
        }
        .into());
    }

    // ── Order book (REST) — depth sizing + liquidity verification ───────
    let up_book = get_order_book(&client, up_asset_id).await?;
    let up_depth = calculate_total_size(&up_book.asks)?;
    let down_book = get_order_book(&client, down_asset_id).await?;
    let down_depth = calculate_total_size(&down_book.asks)?;

    // Verify both sides have actual ask liquidity on the REST book.
    // If one side is empty, FAK will get zero fills → one-sided exposure.
    let up_best_ask: Option<f64> = up_book.asks.first().and_then(|l| l.price.parse().ok());
    let down_best_ask: Option<f64> = down_book.asks.first().and_then(|l| l.price.parse().ok());

    if up_best_ask.is_none() || down_best_ask.is_none() {
        return Err(anyhow!(
            "No ask liquidity on REST book — UP: {} DOWN: {}. Skipping to avoid one-sided fill.",
            if up_best_ask.is_some() { "OK" } else { "EMPTY" },
            if down_best_ask.is_some() { "OK" } else { "EMPTY" },
        ));
    }

    let up_book_price = up_best_ask.unwrap();
    let down_book_price = down_best_ask.unwrap();
    let book_sum = up_book_price + down_book_price;

    // Validate the arb against the REAL order book ask prices (what we
    // actually pay with FAK).  The WS can report stale/phantom prices
    // while the actual book has different asks.  No real arb exists if
    // best_ask_1 + best_ask_2 >= 100c.
    if book_sum >= 1.0 {
        return Err(anyhow!(
            "REST book asks sum to {:.2}c (UP {:.2}c + DOWN {:.2}c) >= 100c. No real arb at the spread.",
            book_sum * 100.0, up_book_price * 100.0, down_book_price * 100.0
        ));
    }

    // Take 50% of the thinner side's depth — smaller orders fill more reliably
    let liquidity_shares = (up_depth.min(down_depth) * 0.5).floor();

    // ── Pricing: REST book best ask + 1c buffer as FAK limit price ───────
    // Use the REST book price (not WS) for the limit — this is the actual
    // price we can fill at.  The +1c buffer absorbs minor drift.
    let up_order_price = ((up_book_price + 0.01) * 100.0).ceil() / 100.0;
    let down_order_price = ((down_book_price + 0.01) * 100.0).ceil() / 100.0;

    eprintln!(
        "Pricing — WS ask: UP={:.2}c DOWN={:.2}c | Book ask: UP={:.2}c DOWN={:.2}c (+1c) | depth: UP={:.0} DOWN={:.0}",
        up_ask * 100.0, down_ask * 100.0,
        up_book_price * 100.0, down_book_price * 100.0,
        up_depth, down_depth
    );

    let cost_per_pair = up_order_price + down_order_price;

    let available = balance - MIN_BALANCE_USDC;
    let affordable_shares = (available / cost_per_pair).floor();
    // Cap so the more expensive leg never exceeds half the available balance.
    // This ensures we always have enough left for the second leg even with
    // asymmetric prices (e.g. UP=56c, DOWN=15c).
    let max_expensive_leg = up_order_price.max(down_order_price);
    let half_balance_shares = (available / 2.0 / max_expensive_leg).floor();
    let buy_shares = liquidity_shares
        .min(affordable_shares)
        .min(half_balance_shares) as u64;

    const MIN_SHARES: u64 = 5;
    if buy_shares < MIN_SHARES {
        return Err(anyhow!(
            "Only {} shares possible (min {}). liquidity={:.0}, affordable={:.0}, balance=${:.2}",
            buy_shares,
            MIN_SHARES,
            liquidity_shares,
            affordable_shares,
            balance
        ));
    }

    // ═══════════════════════════════════════════════════════════════════════
    //  PHASE 1: Pre-build & sign BOTH orders as FAK before sending.
    //  No network calls between the two signs — eliminates signing delay.
    //  Uses REST book ask prices so maker_amount accurately reflects the cost.
    // ═══════════════════════════════════════════════════════════════════════
    let up_salt = now_ms() as u64;
    let down_salt = up_salt + 1;

    eprintln!(
        "Building FAK orders — {} shares × UP {:.2}c + DOWN {:.2}c = {:.2}c/pair, est ${:.4}",
        buy_shares, up_order_price * 100.0, down_order_price * 100.0,
        cost_per_pair * 100.0, cost_per_pair * buy_shares as f64
    );

    let up_order = build_order_request(
        wallet, up_asset_id, buy_shares, up_order_price, "BUY", fee_bps, up_salt, "FAK", 0,
    )
    .await?;
    let down_order = build_order_request(
        wallet, down_asset_id, buy_shares, down_order_price, "BUY", fee_bps, down_salt, "FAK", 0,
    )
    .await?;

    // ═══════════════════════════════════════════════════════════════════════
    //  PHASE 2: Submit BOTH in a single batch request.
    //  Both hit the matching engine in one HTTP call — microseconds apart.
    // ═══════════════════════════════════════════════════════════════════════
    let batch_results = place_batch_orders(&client, wallet, vec![up_order, down_order])
        .await
        .context("batch order submission failed")?;

    if batch_results.len() < 2 {
        return Err(anyhow!(
            "Batch returned {} results (expected 2)",
            batch_results.len()
        ));
    }

    let up_res = &batch_results[0];
    let down_res = &batch_results[1];

    eprintln!(
        "Batch results — UP: success={} status={} orderID={} takingAmt={} makingAmt={} err={}",
        up_res.success, up_res.status, up_res.order_id,
        up_res.taking_amount, up_res.making_amount, up_res.error_msg
    );
    eprintln!(
        "Batch results — DOWN: success={} status={} orderID={} takingAmt={} makingAmt={} err={}",
        down_res.success, down_res.status, down_res.order_id,
        down_res.taking_amount, down_res.making_amount, down_res.error_msg
    );

    // ═══════════════════════════════════════════════════════════════════════
    //  PHASE 3: Determine actual fill sizes for both legs.
    //  FAK can partially fill — we need exact numbers.
    //  Wait briefly for matching engine to finalize, then poll both in parallel.
    // ═══════════════════════════════════════════════════════════════════════
    tokio::time::sleep(Duration::from_millis(500)).await;

    let (up_filled, down_filled) = tokio::join!(
        determine_fill_shares(&client, wallet, up_res, buy_shares, up_order_price),
        determine_fill_shares(&client, wallet, down_res, buy_shares, down_order_price),
    );

    eprintln!(
        "Fill results — UP: {}/{} shares | DOWN: {}/{} shares",
        up_filled, buy_shares, down_filled, buy_shares
    );

    // ═══════════════════════════════════════════════════════════════════════ 
    //  PHASE 4: Handle results — sell back excess if mismatched.
    // ═══════════════════════════════════════════════════════════════════════
    let matched = up_filled.min(down_filled);

    // Both legs got nothing — no capital committed
    if matched == 0 && up_filled == 0 && down_filled == 0 {
        return Err(anyhow!(
            "Both FAK orders unfilled. UP: {} | DOWN: {}",
            up_res.error_msg,
            down_res.error_msg
        ));
    }

    // Sell back excess on whichever side filled more
    let excess_up = up_filled.saturating_sub(matched);
    let excess_down = down_filled.saturating_sub(matched);
    let mut sellback_note = String::new();

    if excess_up > 0 {
        eprintln!("Mismatch: selling back {} excess UP shares", excess_up);
        match sell_back_shares(&client, wallet, up_asset_id, excess_up, fee_bps).await {
            Ok(oid) => {
                sellback_note = format!("Sold {} UP (order {})", excess_up, &oid[..10]);
                eprintln!("{}", sellback_note);
            }
            Err(e) => {
                sellback_note = format!("FAILED to sell {} UP: {:#}", excess_up, e);
                eprintln!("CRITICAL: {}", sellback_note);
            }
        }
    }

    if excess_down > 0 {
        eprintln!("Mismatch: selling back {} excess DOWN shares", excess_down);
        match sell_back_shares(&client, wallet, down_asset_id, excess_down, fee_bps).await {
            Ok(oid) => {
                sellback_note = format!("Sold {} DOWN (order {})", excess_down, &oid[..10]);
                eprintln!("{}", sellback_note);
            }
            Err(e) => {
                sellback_note = format!("FAILED to sell {} DOWN: {:#}", excess_down, e);
                eprintln!("CRITICAL: {}", sellback_note);
            }
        }
    }

    // If one leg filled but the other got nothing — sell-back was already attempted above
    if matched == 0 {
        return Err(anyhow!(
            "One-sided fill (UP={}, DOWN={}). Sell-back: {}",
            up_filled,
            down_filled,
            sellback_note
        ));
    }

    // ═══════════════════════════════════════════════════════════════════════
    //  SUCCESS: We have `matched` shares on both sides.
    // ═══════════════════════════════════════════════════════════════════════
    let total_spent = (up_order_price + down_order_price) * matched as f64;
    let balance_after = balance - total_spent;

    Ok((
        TradeResult {
            shares_bought: matched,
            total_spent,
        },
        TradeDetails {
            balance_before: balance,
            balance_after,
            up_order_id: up_res.order_id.clone(),
            up_status: up_res.status.clone(),
            down_order_id: down_res.order_id.clone(),
            down_status: down_res.status.clone(),
            up_fee_bps: fee_bps,
            down_fee_bps: fee_bps,
            up_depth,
            down_depth,
            requested_shares: buy_shares,
            up_filled,
            down_filled,
        },
    ))
}

/// Sell back shares with guaranteed recovery.
/// Uses a 2-second settlement delay, then GTD sell orders with progressive
/// pricing across 3 attempts.  Each attempt rests on the book for up to 15s
/// to catch incoming bid liquidity.
async fn sell_back_shares(
    client: &Client,
    wallet: &Arc<TradingWallet>,
    asset_id: &str,
    shares: u64,
    fee_bps: u64,
) -> Result<String> {
    // Settlement delay — wait for shares to be credited to internal balance
    eprintln!(
        "Sell-back: waiting 2s for settlement before selling {} shares of {}",
        shares, asset_id
    );
    tokio::time::sleep(Duration::from_secs(2)).await;

    let slippages = [0.03, 0.08, 0.15]; // 3%, 8%, 15% below best bid
    let retry_delays_s = [0u64, 3, 5]; // inter-attempt delays

    for (attempt, (slippage, delay)) in slippages.iter().zip(retry_delays_s.iter()).enumerate() {
        if *delay > 0 {
            tokio::time::sleep(Duration::from_secs(*delay)).await;
        }

        // Re-fetch order book each attempt for fresh best bid
        let book = match get_order_book(client, asset_id).await {
            Ok(b) => b,
            Err(e) => {
                eprintln!(
                    "Sell-back attempt {}: failed to fetch order book: {:#}",
                    attempt + 1,
                    e
                );
                continue;
            }
        };

        if book.bids.is_empty() {
            eprintln!(
                "Sell-back attempt {}: no bids in order book",
                attempt + 1
            );
            continue;
        }

        let best_bid: f64 = match book.bids[0].price.parse() {
            Ok(p) => p,
            Err(_) => continue,
        };
        let sell_price = ((best_bid - slippage) * 100.0).round() / 100.0;
        let sell_price = sell_price.max(0.01); // floor at 1 cent
        let expiration_secs = (now_ms() / 1000) as u64 + 90; // 60s minimum + 30s effective

        let sell_fee = get_fee_rate(client, asset_id).await.unwrap_or(fee_bps);
        let salt = now_ms() as u64 + 100 + attempt as u64;

        eprintln!(
            "Sell-back attempt {}: {} shares at {:.2}c (best bid {:.2}c, slippage {:.0}%)",
            attempt + 1,
            shares,
            sell_price * 100.0,
            best_bid * 100.0,
            slippage * 100.0
        );

        let sell_order = match build_order_request(
            wallet, asset_id, shares, sell_price, "SELL", sell_fee, salt, "GTD", expiration_secs,
        )
        .await
        {
            Ok(o) => o,
            Err(e) => {
                eprintln!(
                    "Sell-back attempt {}: build order failed: {:#}",
                    attempt + 1,
                    e
                );
                continue;
            }
        };

        let res = match place_single_order(client, wallet, sell_order).await {
            Ok(r) => r,
            Err(e) => {
                eprintln!(
                    "Sell-back attempt {}: place order failed: {:#}",
                    attempt + 1,
                    e
                );
                continue;
            }
        };

        // Immediately filled
        if res.success && res.status.eq_ignore_ascii_case("MATCHED") {
            eprintln!(
                "Sell-back attempt {}: fully filled immediately (order {})",
                attempt + 1,
                res.order_id
            );
            return Ok(res.order_id);
        }

        // Order is LIVE on the book — poll for up to 15 seconds
        if res.success && !res.order_id.is_empty() {
            eprintln!(
                "Sell-back attempt {}: order {} LIVE, polling for fills...",
                attempt + 1,
                res.order_id
            );
            for poll_i in 0..15 {
                tokio::time::sleep(Duration::from_secs(1)).await;
                if let Ok(status) = get_order_status(client, wallet, &res.order_id).await {
                    let matched: f64 = status.size_matched.parse().unwrap_or(0.0);
                    if matched >= shares as f64 {
                        eprintln!(
                            "Sell-back attempt {}: filled after {}s (order {})",
                            attempt + 1,
                            poll_i + 1,
                            res.order_id
                        );
                        return Ok(res.order_id);
                    }
                }
            }
            // Not fully filled after 15s — cancel remainder, try more aggressive price
            eprintln!(
                "Sell-back attempt {}: not filled after 15s, cancelling {}",
                attempt + 1,
                res.order_id
            );
            let _ = cancel_order(client, wallet, &res.order_id).await;
        } else {
            eprintln!(
                "Sell-back attempt {}: rejected: {}",
                attempt + 1,
                res.error_msg
            );
        }
    }

    Err(anyhow!(
        "sell-back failed after {} attempts for {} shares of {}",
        slippages.len(),
        shares,
        asset_id
    ))
}

async fn get_fee_rate(client: &Client, token_id: &str) -> Result<u64> {
    let url = format!("{CLOB_API}/markets/fee-rate?token_id={token_id}");
    let resp = client.get(&url).send().await.context("fetch fee rate")?;

    let raw = resp.text().await.context("read fee rate response")?;
    let parsed: Value =
        serde_json::from_str(&raw).with_context(|| format!("parse fee rate JSON: {raw}"))?;

    let fee = parsed
        .get("base_fee")
        .and_then(|v| v.as_u64())
        .ok_or_else(|| anyhow!("missing base_fee in fee rate response: {raw}"))?;

    Ok(fee)
}

async fn get_order_book(client: &Client, token_id: &str) -> Result<OrderBook> {
    let url = format!("{CLOB_API}/book?token_id={}", token_id);
    let resp = client.get(&url).send().await.context("fetch order book")?;

    let mut book: OrderBook = resp.json().await.context("parse order book")?;

    // CLOB API returns asks in arbitrary/descending order — sort ascending so
    // asks[0] is the cheapest (best) ask.  Sort bids descending so bids[0] is
    // the highest (best) bid.
    book.asks.sort_by(|a, b| {
        let pa: f64 = a.price.parse().unwrap_or(f64::MAX);
        let pb: f64 = b.price.parse().unwrap_or(f64::MAX);
        pa.partial_cmp(&pb).unwrap_or(std::cmp::Ordering::Equal)
    });
    book.bids.sort_by(|a, b| {
        let pa: f64 = a.price.parse().unwrap_or(0.0);
        let pb: f64 = b.price.parse().unwrap_or(0.0);
        pb.partial_cmp(&pa).unwrap_or(std::cmp::Ordering::Equal)
    });

    Ok(book)
}

// FIX 6: Renamed and corrected — sums total available size across top 5 ask levels
// instead of computing the mean, giving a true picture of fillable liquidity.
fn calculate_total_size(levels: &[OrderBookLevel]) -> Result<f64> {
    if levels.is_empty() {
        return Ok(0.0);
    }

    let total_size: f64 = levels
        .iter()
        .take(5) // Consider top 5 levels
        .filter_map(|level| level.size.parse::<f64>().ok())
        .sum();

    Ok(total_size)
}

// ── CTF Position Redemption (via polymarket-client-sdk) ──────────────────────
//
// After a binary market resolves, outcome shares are redeemable for USDC via
// the ConditionalTokens contract.  We use the polymarket-client-sdk CtfClient
// which handles ABI encoding, tx signing, and confirmation internally.
// Called at startup (sweep old windows) and after every window close.
async fn redeem_positions(private_key: &str, condition_id_hex: &str) -> Result<()> {
    let ankr_key = env::var(ANKR_API_KEY_ENV)
        .with_context(|| format!("Missing env var '{ANKR_API_KEY_ENV}'"))?;
    let rpc_url = format!("https://rpc.ankr.com/polygon/{}", ankr_key.trim());

    let signer = LocalSigner::from_str(private_key.trim())
        .context("parse private key for redeem")?
        .with_chain_id(Some(POLYGON));

    let provider = ProviderBuilder::new()
        .wallet(signer)
        .connect(&rpc_url)
        .await
        .context("connect provider for redeem")?;

    let ctf_client = CtfClient::new(provider, POLYGON).context("init ctf client")?;

    let collateral: AlloyAddress = USDC_E_POLYGON.parse().context("parse USDC.e")?;
    let condition_id: B256 = condition_id_hex.parse().context("parse conditionId")?;

    let mut req = RedeemPositionsRequest::for_binary_market(collateral, condition_id);
    req.index_sets = vec![AlloyU256::from(1), AlloyU256::from(2)];

    ctf_client
        .redeem_positions(&req)
        .await
        .with_context(|| format!("redeem condition {condition_id:#x}"))?;

    Ok(())
}

/// Checks the pending redemptions JSON file and attempts to redeem any markets
/// whose `redeem_after_ts` has passed.  Successfully redeemed entries are removed
/// from the file.  Failed (non-revert) redemptions trigger a Discord error alert.
/// Returns the count of successfully redeemed markets.
async fn redeem_pending_markets(private_key: &str) -> u32 {
    let now_secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs() as i64;

    let redemptions = load_pending_redemptions();
    if redemptions.is_empty() {
        return 0;
    }

    let mut redeemed = 0u32;
    let mut remaining: Vec<PendingRedemption> = Vec::new();

    for entry in &redemptions {
        if now_secs < entry.redeem_after_ts {
            // Not ready yet — keep for later
            remaining.push(entry.clone());
            continue;
        }

        eprintln!(
            "Attempting redemption: {} (condition {})",
            entry.slug, entry.condition_id
        );

        match redeem_positions(private_key, &entry.condition_id).await {
            Ok(_) => {
                eprintln!("  Redeemed successfully: {}", entry.slug);
                redeemed += 1;
                // Do not add to remaining — it's done
            }
            Err(e) => {
                let msg = format!("{e:#}");
                if msg.contains("revert") || msg.contains("insufficient") {
                    // "execution reverted" means oracle hasn't resolved yet, or
                    // already redeemed. Keep it for a bit longer, but remove if
                    // it's been more than 1 hour past the scheduled time.
                    if now_secs - entry.redeem_after_ts > 3600 {
                        eprintln!(
                            "  Removing stale redemption (>1h overdue): {} — {:#}",
                            entry.slug, e
                        );
                        let alert = format!(
                            "Redemption failed after 1h for `{}`:\n```\n{}\n```",
                            entry.slug, msg
                        );
                        if let Err(ae) = send_error_alert(&alert).await {
                            eprintln!("  Failed to send redeem alert: {ae:#}");
                        }
                    } else {
                        remaining.push(entry.clone());
                    }
                } else {
                    // Unexpected error — alert and keep for retry
                    eprintln!("  Redeem error for {}: {:#}", entry.slug, e);
                    let alert = format!(
                        "Redemption error for `{}`:\n```\n{}\n```",
                        entry.slug, msg
                    );
                    if let Err(ae) = send_error_alert(&alert).await {
                        eprintln!("  Failed to send redeem alert: {ae:#}");
                    }
                    remaining.push(entry.clone());
                }
            }
        }
    }

    // Only rewrite the file if something changed
    if remaining.len() != redemptions.len() {
        save_pending_redemptions(&remaining);
    }

    redeemed
}

async fn get_balance(client: &Client, address: &Address) -> Result<f64> {
    // Call USDC balanceOf(address) via raw eth_call on Ankr's Polygon RPC.
    // Reads ANKR_API_KEY from the .env file.
    let ankr_key = env::var(ANKR_API_KEY_ENV).with_context(|| {
        format!("Missing env var '{ANKR_API_KEY_ENV}' — add it to your .env file")
    })?;
    let ankr_key = ankr_key.trim().to_string();
    let rpc_url = format!("https://rpc.ankr.com/polygon/{}", ankr_key);

    let addr_hex = format!("{:x}", address); // 40 hex chars, no 0x prefix
    // ABI-encode: 12 zero-bytes padding + 20-byte address = 32-byte word
    let calldata = format!("0x70a08231{:0>64}", addr_hex);

    let body = json!({
        "jsonrpc": "2.0",
        "method": "eth_call",
        "params": [
            { "to": USDC_E_POLYGON, "data": calldata },
            "latest"
        ],
        "id": 1
    });

    let resp = client
        .post(&rpc_url)
        .json(&body)
        .send()
        .await
        .context("eth_call request failed")?;

    let raw = resp.text().await.context("read eth_call response")?;
    let parsed: Value =
        serde_json::from_str(&raw).with_context(|| format!("parse eth_call JSON: {raw}"))?;

    if let Some(err) = parsed.get("error") {
        return Err(anyhow!("eth_call RPC error: {err}"));
    }

    // Result is a 0x-prefixed 32-byte hex integer
    let hex_result = parsed
        .get("result")
        .and_then(|v| v.as_str())
        .unwrap_or("0x0")
        .trim_start_matches("0x");

    let raw_amount = u128::from_str_radix(hex_result, 16).unwrap_or(0);
    // USDC on Polygon has 6 decimals
    Ok(raw_amount as f64 / 1_000_000.0)
}

// ── Allowance helpers ────────────────────────────────────────────────────────

// allowance(owner, spender) selector = keccak256("allowance(address,address)")[..4] = 0xdd62ed3e
async fn get_allowance(client: &Client, owner: &Address, spender: &str) -> Result<f64> {
    let ankr_key = env::var(ANKR_API_KEY_ENV)
        .with_context(|| format!("Missing env var '{ANKR_API_KEY_ENV}'"))?;
    let rpc_url = format!("https://rpc.ankr.com/polygon/{}", ankr_key.trim());

    let owner_hex = format!("{:x}", owner);
    let spender_hex = spender.trim_start_matches("0x");
    // ABI-encode two addresses: each padded to 32 bytes
    let calldata = format!("0xdd62ed3e{:0>64}{:0>64}", owner_hex, spender_hex);

    let body = json!({
        "jsonrpc": "2.0",
        "method": "eth_call",
        "params": [{ "to": USDC_E_POLYGON, "data": calldata }, "latest"],
        "id": 1
    });

    let resp = client
        .post(&rpc_url)
        .json(&body)
        .send()
        .await
        .context("eth_call allowance")?;
    let raw = resp.text().await.context("read allowance response")?;
    let parsed: Value =
        serde_json::from_str(&raw).with_context(|| format!("parse allowance JSON: {raw}"))?;

    if let Some(err) = parsed.get("error") {
        return Err(anyhow!("allowance eth_call error: {err}"));
    }

    let hex = parsed
        .get("result")
        .and_then(|v| v.as_str())
        .unwrap_or("0x0")
        .trim_start_matches("0x");
    let raw_amount = u128::from_str_radix(hex, 16).unwrap_or(0);
    Ok(raw_amount as f64 / 1_000_000.0)
}

// Sends an ERC-20 approve(spender, uint256::MAX) tx via eth_sendRawTransaction.
// Uses the wallet's private key to sign the transaction on-chain.
async fn ensure_allowance(client: &Client, wallet: &TradingWallet, spender: &str) -> Result<()> {
    let allowance = get_allowance(client, &wallet.address, spender).await?;
    if allowance >= 1000.0 {
        return Ok(());
    }

    let ankr_key = env::var(ANKR_API_KEY_ENV)
        .with_context(|| format!("Missing env var '{ANKR_API_KEY_ENV}'"))?;
    let rpc_url = format!("https://rpc.ankr.com/polygon/{}", ankr_key.trim());

    // Get nonce
    let nonce_body = json!({
        "jsonrpc": "2.0", "method": "eth_getTransactionCount",
        "params": [format!("{:#x}", wallet.address), "latest"], "id": 1
    });
    let nonce_resp: Value = client
        .post(&rpc_url)
        .json(&nonce_body)
        .send()
        .await
        .context("get nonce")?
        .json()
        .await
        .context("parse nonce")?;
    let nonce = nonce_resp["result"]
        .as_str()
        .and_then(|s| u64::from_str_radix(s.trim_start_matches("0x"), 16).ok())
        .ok_or_else(|| anyhow!("could not parse nonce: {nonce_resp}"))?;

    // Get gas price
    let gas_body = json!({"jsonrpc":"2.0","method":"eth_gasPrice","params":[],"id":1});
    let gas_resp: Value = client
        .post(&rpc_url)
        .json(&gas_body)
        .send()
        .await
        .context("get gas price")?
        .json()
        .await
        .context("parse gas price")?;
    let gas_price = gas_resp["result"]
        .as_str()
        .and_then(|s| u128::from_str_radix(s.trim_start_matches("0x"), 16).ok())
        .ok_or_else(|| anyhow!("could not parse gas price: {gas_resp}"))?;

    // approve(spender, 2^256-1) calldata — selector 0x095ea7b3
    let spender_hex = spender.trim_start_matches("0x");
    // ABI-encode: padded spender address + uint256 max (32 bytes of 0xff)
    let calldata_hex = format!("095ea7b3{:0>64}{}", spender_hex, "f".repeat(64));
    let calldata_bytes = hex::decode(&calldata_hex).context("decode approve calldata")?;

    // Build TypedTransaction (Legacy) so we can call tx.rlp_signed()
    use ethers::types::transaction::eip2718::TypedTransaction;
    let tx = TypedTransaction::Legacy(ethers::types::TransactionRequest {
        from: Some(wallet.address),
        to: Some(USDC_E_POLYGON.parse::<Address>().unwrap().into()),
        nonce: Some(U256::from(nonce)),
        gas: Some(U256::from(100_000u64)),
        gas_price: Some(U256::from(gas_price * 3)), // 3x = high priority for fast inclusion
        data: Some(calldata_bytes.into()),
        value: Some(U256::zero()),
        chain_id: Some(U64::from(CHAIN_ID)),
        ..Default::default()
    });

    // sign_transaction fills in the chain_id and returns the Signature
    let sig = wallet
        .wallet
        .sign_transaction(&tx)
        .await
        .map_err(|e| anyhow!("sign approve tx: {e}"))?;

    // rlp_signed encodes the tx + signature into the raw bytes ready for broadcast
    let raw_tx = format!("0x{}", hex::encode(tx.rlp_signed(&sig)));

    let send_body = json!({
        "jsonrpc": "2.0", "method": "eth_sendRawTransaction",
        "params": [raw_tx], "id": 1
    });
    let send_resp: Value = client
        .post(&rpc_url)
        .json(&send_body)
        .send()
        .await
        .context("send approve tx")?
        .json()
        .await
        .context("parse send response")?;

    if let Some(err) = send_resp.get("error") {
        return Err(anyhow!("approve tx failed: {err}"));
    }

    let tx_hash = send_resp["result"]
        .as_str()
        .ok_or_else(|| anyhow!("no tx hash in response: {send_resp}"))?;

    // Poll for receipt (up to 30 seconds)
    for _ in 0..30 {
        tokio::time::sleep(Duration::from_secs(1)).await;
        let receipt_body = json!({
            "jsonrpc": "2.0", "method": "eth_getTransactionReceipt",
            "params": [tx_hash], "id": 1
        });
        let receipt: Value = client
            .post(&rpc_url)
            .json(&receipt_body)
            .send()
            .await
            .context("get receipt")?
            .json()
            .await
            .context("parse receipt")?;
        if let Some(r) = receipt.get("result").filter(|v| !v.is_null()) {
            let status = r["status"].as_str().unwrap_or("0x0");
            if status == "0x1" {
                return Ok(());
            } else {
                return Err(anyhow!(
                    "Approve tx reverted. Check wallet has MATIC for gas."
                ));
            }
        }
    }

    Err(anyhow!(
        "Approve tx not confirmed within 30s. Check Polygonscan: {tx_hash}"
    ))
}

// ── ERC-1155 approval for ConditionalTokens (needed for SELL orders) ────────
//
// The CTF Exchange must call transferFrom on the ConditionalTokens (ERC-1155)
// contract to settle SELL orders.  This requires setApprovalForAll(operator, true).

/// isApprovedForAll(address,address) — selector 0xe985e9c5
async fn is_approved_for_all(
    client: &Client,
    owner: &Address,
    operator: &str,
    contract: &str,
) -> Result<bool> {
    let ankr_key = env::var(ANKR_API_KEY_ENV)
        .with_context(|| format!("Missing env var '{ANKR_API_KEY_ENV}'"))?;
    let rpc_url = format!("https://rpc.ankr.com/polygon/{}", ankr_key.trim());

    let owner_hex = format!("{:x}", owner);
    let operator_hex = operator.trim_start_matches("0x");
    let calldata = format!("e985e9c5{:0>64}{:0>64}", owner_hex, operator_hex);

    let body = json!({
        "jsonrpc": "2.0",
        "method": "eth_call",
        "params": [{"to": contract, "data": format!("0x{calldata}")}, "latest"],
        "id": 1
    });

    let resp = client
        .post(&rpc_url)
        .json(&body)
        .send()
        .await
        .context("eth_call isApprovedForAll")?;
    let raw = resp.text().await.context("read isApprovedForAll response")?;
    let parsed: Value = serde_json::from_str(&raw)
        .with_context(|| format!("parse isApprovedForAll JSON: {raw}"))?;

    if let Some(err) = parsed.get("error") {
        return Err(anyhow!("isApprovedForAll error: {err}"));
    }

    let hex = parsed
        .get("result")
        .and_then(|v| v.as_str())
        .unwrap_or("0x0")
        .trim_start_matches("0x");
    let val = u128::from_str_radix(hex, 16).unwrap_or(0);
    Ok(val != 0)
}

/// Calls setApprovalForAll(CTF_EXCHANGE_ADDRESS, true) on the ConditionalTokens
/// contract if not already approved.  This is required for SELL orders.
async fn ensure_ctf_token_approval(client: &Client, wallet: &TradingWallet) -> Result<()> {
    let approved = is_approved_for_all(
        client,
        &wallet.address,
        CTF_EXCHANGE_ADDRESS,
        CONDITIONAL_TOKENS_ADDRESS,
    )
    .await?;

    if approved {
        return Ok(());
    }

    eprintln!("ERC-1155 approval missing — sending setApprovalForAll tx...");

    let ankr_key = env::var(ANKR_API_KEY_ENV)
        .with_context(|| format!("Missing env var '{ANKR_API_KEY_ENV}'"))?;
    let rpc_url = format!("https://rpc.ankr.com/polygon/{}", ankr_key.trim());

    // Nonce
    let nonce_body = json!({
        "jsonrpc": "2.0", "method": "eth_getTransactionCount",
        "params": [format!("{:#x}", wallet.address), "latest"], "id": 1
    });
    let nonce_resp: Value = client
        .post(&rpc_url)
        .json(&nonce_body)
        .send()
        .await
        .context("get nonce for setApprovalForAll")?
        .json()
        .await?;
    let nonce = nonce_resp["result"]
        .as_str()
        .and_then(|s| u64::from_str_radix(s.trim_start_matches("0x"), 16).ok())
        .ok_or_else(|| anyhow!("bad nonce: {nonce_resp}"))?;

    // Gas price
    let gas_body = json!({"jsonrpc":"2.0","method":"eth_gasPrice","params":[],"id":1});
    let gas_resp: Value = client
        .post(&rpc_url)
        .json(&gas_body)
        .send()
        .await
        .context("get gas price")?
        .json()
        .await?;
    let gas_price = gas_resp["result"]
        .as_str()
        .and_then(|s| u128::from_str_radix(s.trim_start_matches("0x"), 16).ok())
        .ok_or_else(|| anyhow!("could not parse gas price: {gas_resp}"))?;

    // setApprovalForAll(address operator, bool approved) — selector 0xa22cb465
    let operator_hex = CTF_EXCHANGE_ADDRESS.trim_start_matches("0x");
    let calldata_hex = format!(
        "a22cb465{:0>64}{:0>64}",
        operator_hex,
        "1" // true
    );
    let calldata_bytes = hex::decode(&calldata_hex).context("decode setApprovalForAll calldata")?;

    use ethers::types::transaction::eip2718::TypedTransaction;
    let tx = TypedTransaction::Legacy(ethers::types::TransactionRequest {
        from: Some(wallet.address),
        to: Some(
            CONDITIONAL_TOKENS_ADDRESS
                .parse::<Address>()
                .unwrap()
                .into(),
        ),
        nonce: Some(U256::from(nonce)),
        gas: Some(U256::from(100_000u64)),
        gas_price: Some(U256::from(gas_price * 3)),
        data: Some(calldata_bytes.into()),
        value: Some(U256::zero()),
        chain_id: Some(U64::from(CHAIN_ID)),
        ..Default::default()
    });

    let sig = wallet
        .wallet
        .sign_transaction(&tx)
        .await
        .map_err(|e| anyhow!("sign setApprovalForAll tx: {e}"))?;
    let raw_tx = format!("0x{}", hex::encode(tx.rlp_signed(&sig)));

    let send_body = json!({
        "jsonrpc": "2.0", "method": "eth_sendRawTransaction",
        "params": [raw_tx], "id": 1
    });
    let send_resp: Value = client
        .post(&rpc_url)
        .json(&send_body)
        .send()
        .await
        .context("send setApprovalForAll tx")?
        .json()
        .await
        .context("parse send response")?;

    if let Some(err) = send_resp.get("error") {
        return Err(anyhow!("setApprovalForAll tx failed: {err}"));
    }

    let tx_hash = send_resp["result"]
        .as_str()
        .ok_or_else(|| anyhow!("no tx hash in response: {send_resp}"))?;

    // Poll for receipt (up to 30 seconds)
    for _ in 0..30 {
        tokio::time::sleep(Duration::from_secs(1)).await;
        let receipt_body = json!({
            "jsonrpc": "2.0", "method": "eth_getTransactionReceipt",
            "params": [tx_hash], "id": 1
        });
        let receipt: Value = client
            .post(&rpc_url)
            .json(&receipt_body)
            .send()
            .await
            .context("get receipt")?
            .json()
            .await
            .context("parse receipt")?;
        if let Some(r) = receipt.get("result").filter(|v| !v.is_null()) {
            let status = r["status"].as_str().unwrap_or("0x0");
            if status == "0x1" {
                eprintln!("ERC-1155 approval set successfully: {tx_hash}");
                return Ok(());
            } else {
                return Err(anyhow!(
                    "setApprovalForAll tx reverted. Check wallet has MATIC for gas."
                ));
            }
        }
    }

    Err(anyhow!(
        "setApprovalForAll tx not confirmed within 30s. Check Polygonscan: {tx_hash}"
    ))
}

// ── L1 EIP-712 Auth ─────────────────────────────────────────────────────────
//
// Signs the ClobAuth struct using ethers-rs TypedData — matches the official
// TypeScript client exactly (same domain, same field encoding).
async fn l1_auth_signature(
    wallet: &LocalWallet,
    address: Address,
    timestamp: i64,
    nonce: u64,
) -> Result<String> {
    use ethers::types::transaction::eip712::TypedData;

    let typed_data: TypedData = serde_json::from_value(json!({
        "primaryType": "ClobAuth",
        "domain": {
            "name":    "ClobAuthDomain",
            "version": "1",
            "chainId": CHAIN_ID
        },
        "types": {
            "EIP712Domain": [
                {"name": "name",    "type": "string"},
                {"name": "version", "type": "string"},
                {"name": "chainId", "type": "uint256"}
            ],
            "ClobAuth": [
                {"name": "address",   "type": "address"},
                {"name": "timestamp", "type": "string"},
                {"name": "nonce",     "type": "uint256"},
                {"name": "message",   "type": "string"}
            ]
        },
        "message": {
            "address":   format!("{:#x}", address),
            "timestamp": timestamp.to_string(),
            "nonce":     nonce,
            "message":   "This message attests that I control the given wallet"
        }
    }))
    .context("build ClobAuth TypedData")?;

    let sig = wallet
        .sign_typed_data(&typed_data)
        .await
        .map_err(|e| anyhow!("sign_typed_data (L1 ClobAuth) failed: {e}"))?;

    Ok(format!("0x{}", hex::encode(sig.to_vec())))
}

// ── L2 HMAC-SHA256 Auth ───────────────────────────────────────────────────────
//
// Produces the POLY_SIGNATURE header for authenticated CLOB API calls.
// message = timestamp + METHOD + path + body
fn l2_signature(
    secret: &str,
    timestamp: i64,
    method: &str,
    path: &str,
    body: &str,
) -> Result<String> {
    let message = format!("{}{}{}{}", timestamp, method.to_uppercase(), path, body);
    let secret_bytes = BASE64
        .decode(secret)
        .context("decode L2 secret (not valid base64)")?;
    let mut mac = Hmac::<Sha256>::new_from_slice(&secret_bytes)
        .map_err(|e| anyhow!("HMAC key error: {e}"))?;
    mac.update(message.as_bytes());
    Ok(BASE64.encode(mac.finalize().into_bytes()))
}

// ── Obtain/derive API credentials via L1 auth ─────────────────────────────────
async fn get_or_create_api_creds(
    wallet: &LocalWallet,
    address: Address,
    client: &Client,
) -> Result<ApiCredentials> {
    let timestamp = now_ms() / 1000; // seconds
    let nonce = 0u64;
    // l1_auth_signature is now async (uses TypedData internally)
    let signature = l1_auth_signature(wallet, address, timestamp, nonce).await?;
    let address_str = format!("{:#x}", address);

    // ── Step 1: try GET /derive-api-key (returns existing credentials) ──────
    let derive_resp = client
        .get(format!("{CLOB_API}/auth/derive-api-key"))
        .header("POLY_ADDRESS", &address_str)
        .header("POLY_SIGNATURE", &signature)
        .header("POLY_TIMESTAMP", timestamp.to_string())
        .header("POLY_NONCE", nonce.to_string())
        .send()
        .await
        .context("L1 auth GET /auth/derive-api-key")?;

    let derive_raw = derive_resp.text().await.context("read derive response")?;
    let derive_parsed: Value = serde_json::from_str(&derive_raw)
        .with_context(|| format!("parse derive JSON: {derive_raw}"))?;

    if let (Some(k), Some(s), Some(p)) = (
        derive_parsed.get("apiKey").and_then(|v| v.as_str()),
        derive_parsed.get("secret").and_then(|v| v.as_str()),
        derive_parsed.get("passphrase").and_then(|v| v.as_str()),
    ) {
        return Ok(ApiCredentials {
            api_key: k.to_string(),
            secret: s.to_string(),
            passphrase: p.to_string(),
        });
    }

    // ── Step 2: fall back to POST /api-key (creates new credentials) ────────
    // NOTE: If this returns "Could not create api key", your wallet has not been
    // registered on Polymarket yet. Visit https://polymarket.com, connect wallet
    // 0x5f747b55957ecff985faed31635df8c6fc3677b7, and accept the Terms of Service.
    // After that, restart the bot and credentials will be created automatically.

    // Re-sign with a fresh timestamp for the second request
    let timestamp2 = now_ms() / 1000;
    let signature2 = l1_auth_signature(wallet, address, timestamp2, nonce).await?;

    let create_resp = client
        .post(format!("{CLOB_API}/auth/api-key"))
        .header("POLY_ADDRESS", &address_str)
        .header("POLY_SIGNATURE", &signature2)
        .header("POLY_TIMESTAMP", timestamp2.to_string())
        .header("POLY_NONCE", nonce.to_string())
        .send()
        .await
        .context("L1 auth POST /auth/api-key")?;

    let create_raw = create_resp.text().await.context("read create response")?;
    let create_parsed: Value = serde_json::from_str(&create_raw)
        .with_context(|| format!("parse create JSON: {create_raw}"))?;

    let api_key = create_parsed.get("apiKey").and_then(|v| v.as_str())
        .ok_or_else(|| anyhow!(
            "Could not obtain API credentials.
             Server response: {create_raw}
             
             If you see \"Could not create api key\", your wallet is not registered.
             Fix: Go to https://polymarket.com, connect wallet {address_str}, accept ToS, then restart."
        ))?;
    let secret = create_parsed
        .get("secret")
        .and_then(|v| v.as_str())
        .ok_or_else(|| anyhow!("No secret in create response: {create_raw}"))?;
    let passphrase = create_parsed
        .get("passphrase")
        .and_then(|v| v.as_str())
        .ok_or_else(|| anyhow!("No passphrase in create response: {create_raw}"))?;

    Ok(ApiCredentials {
        api_key: api_key.to_string(),
        secret: secret.to_string(),
        passphrase: passphrase.to_string(),
    })
}

// ── EIP-712 Order Signing ─────────────────────────────────────────────────────
//
// Signs the Polymarket CTF Exchange Order struct using ethers-rs TypedData.
async fn eip712_order_signature(
    wallet: &LocalWallet,
    address: Address,
    token_id: &str,
    maker_amount: u128,
    taker_amount: u128,
    side: u8,
    salt: u64,
    fee_bps: u64,
    expiration: u64,
) -> Result<String> {
    use ethers::types::transaction::eip712::TypedData;

    let typed_data: TypedData = serde_json::from_value(json!({
        "primaryType": "Order",
        "domain": {
            "name":              "Polymarket CTF Exchange",
            "version":           "1",
            "chainId":           CHAIN_ID,
            "verifyingContract": CTF_EXCHANGE_ADDRESS
        },
        "types": {
            "EIP712Domain": [
                {"name": "name",              "type": "string"},
                {"name": "version",           "type": "string"},
                {"name": "chainId",           "type": "uint256"},
                {"name": "verifyingContract", "type": "address"}
            ],
            "Order": [
                {"name": "salt",            "type": "uint256"},
                {"name": "maker",           "type": "address"},
                {"name": "signer",          "type": "address"},
                {"name": "taker",           "type": "address"},
                {"name": "tokenId",         "type": "uint256"},
                {"name": "makerAmount",     "type": "uint256"},
                {"name": "takerAmount",     "type": "uint256"},
                {"name": "expiration",      "type": "uint256"},
                {"name": "nonce",           "type": "uint256"},
                {"name": "feeRateBps",      "type": "uint256"},
                {"name": "side",            "type": "uint8"},
                {"name": "signatureType",   "type": "uint8"}
            ]
        },
        "message": {
            "salt":          salt.to_string(),
            "maker":         format!("{:#x}", address),
            "signer":        format!("{:#x}", address),
            "taker":         ZERO_ADDRESS,
            "tokenId":       token_id,
            "makerAmount":   maker_amount.to_string(),
            "takerAmount":   taker_amount.to_string(),
            "expiration":    expiration.to_string(),
            "nonce":         "0",
            "feeRateBps":    fee_bps.to_string(),
            "side":          side,
            "signatureType": 0u8
        }
    }))
    .context("build Order TypedData")?;

    let sig = wallet
        .sign_typed_data(&typed_data)
        .await
        .map_err(|e| anyhow!("sign_typed_data (Order) failed: {e}"))?;

    Ok(format!("0x{}", hex::encode(sig.to_vec())))
}

// ── Build a signed order request (does NOT send it) ───────────────────────────
async fn build_order_request(
    wallet: &Arc<TradingWallet>,
    token_id: &str,
    size: u64,
    price: f64,
    side: &str,
    fee_bps: u64,
    salt: u64,
    order_type: &str,
    expiration: u64,
) -> Result<CreateOrderRequest> {
    let side_uint: u8 = if side == "BUY" { 0 } else { 1 };

    // Price is already rounded to tick size (0.01) by the caller.
    // Amounts use 6 decimal places (same as USDC).
    // BUY: makerAmount = USDC to spend, takerAmount = tokens to receive.
    // SELL: makerAmount = tokens to give, takerAmount = USDC to receive.
    let (maker_amount, taker_amount) = if side_uint == 0 {
        let maker = (price * size as f64 * 1_000_000.0).round() as u128;
        let taker = size as u128 * 1_000_000;
        (maker, taker)
    } else {
        let maker = size as u128 * 1_000_000;
        let taker = (price * size as f64 * 1_000_000.0).round() as u128;
        (maker, taker)
    };

    // Polymarket minimum maker amount is $1 (1_000_000 in 6-decimal USDC)
    const MIN_MAKER_AMOUNT: u128 = 1_000_000;
    if maker_amount < MIN_MAKER_AMOUNT {
        return Err(anyhow!(
            "Maker amount ${:.4} is below the $1.00 minimum (size={}, price={:.4}). \
             This leg cannot be placed — skipping trade.",
            maker_amount as f64 / 1_000_000.0,
            size,
            price
        ));
    }

    // EIP-712 sign the order
    let signature = eip712_order_signature(
        &wallet.wallet,
        wallet.address,
        token_id,
        maker_amount,
        taker_amount,
        side_uint,
        salt,
        fee_bps,
        expiration,
    )
    .await?;

    let order = PolymarketOrderStruct {
        salt,
        maker: format!("{:#x}", wallet.address),
        signer: format!("{:#x}", wallet.address),
        taker: ZERO_ADDRESS.to_string(),
        token_id: token_id.to_string(),
        maker_amount: maker_amount.to_string(),
        taker_amount: taker_amount.to_string(),
        side: side.to_string(),
        expiration: expiration.to_string(),
        nonce: "0".to_string(),
        fee_rate_bps: fee_bps.to_string(),
        signature,
        signature_type: 0,
    };

    Ok(CreateOrderRequest {
        order,
        owner: wallet.creds.api_key.clone(),
        order_type: order_type.to_string(),
        defer_exec: false,
    })
}

// ── Submit a single order via POST /order ─────────────────────────────────────
async fn place_single_order(
    client: &Client,
    wallet: &Arc<TradingWallet>,
    order: CreateOrderRequest,
) -> Result<BatchOrderResult> {
    let body_str = serde_json::to_string(&order).context("serialise order")?;

    let timestamp = now_ms() / 1000;
    let l2_sig = l2_signature(&wallet.creds.secret, timestamp, "POST", "/order", &body_str)
        .context("compute L2 HMAC for single order")?;

    let url = format!("{CLOB_API}/order");
    let resp = client
        .post(&url)
        .header("Content-Type", "application/json")
        .header("POLY_ADDRESS", format!("{:#x}", wallet.address))
        .header("POLY_SIGNATURE", l2_sig)
        .header("POLY_TIMESTAMP", timestamp.to_string())
        .header("POLY_API_KEY", &wallet.creds.api_key)
        .header("POLY_PASSPHRASE", &wallet.creds.passphrase)
        .body(body_str)
        .send()
        .await
        .context("place single order")?;

    if !resp.status().is_success() {
        let error_text = resp.text().await.unwrap_or_default();
        return Err(anyhow!("Order placement failed: {}", error_text));
    }

    let result: BatchOrderResult = resp.json().await.context("parse single order response")?;

    Ok(result)
}

// ── Cancel an open order via the CLOB API ─────────────────────────────────────
// Fallback when a batch submission partially succeeds: cancel the successful
// leg so we don't hold an unbalanced position.  If the order already filled
// the cancel will fail — the caller sends a Discord alert in that case.
async fn cancel_order(client: &Client, wallet: &Arc<TradingWallet>, order_id: &str) -> Result<()> {
    let timestamp = now_ms() / 1000;
    let body_str = json!({"orderID": order_id}).to_string();
    let l2_sig = l2_signature(
        &wallet.creds.secret,
        timestamp,
        "DELETE",
        "/order",
        &body_str,
    )
    .context("compute L2 HMAC for cancel")?;

    let url = format!("{CLOB_API}/order");
    let resp = client
        .delete(&url)
        .header("Content-Type", "application/json")
        .header("POLY_ADDRESS", format!("{:#x}", wallet.address))
        .header("POLY_SIGNATURE", l2_sig)
        .header("POLY_TIMESTAMP", timestamp.to_string())
        .header("POLY_API_KEY", &wallet.creds.api_key)
        .header("POLY_PASSPHRASE", &wallet.creds.passphrase)
        .body(body_str)
        .send()
        .await
        .context("cancel order request")?;

    if !resp.status().is_success() {
        let error_text = resp.text().await.unwrap_or_default();
        return Err(anyhow!("Cancel order failed: {}", error_text));
    }

    Ok(())
}

// ── Poll order fill status via GET /data/order/{order_hash} ───────────────────
async fn get_order_status(
    client: &Client,
    wallet: &Arc<TradingWallet>,
    order_id: &str,
) -> Result<OpenOrder> {
    let path = format!("/data/order/{}", order_id);
    let timestamp = now_ms() / 1000;
    let l2_sig = l2_signature(&wallet.creds.secret, timestamp, "GET", &path, "")
        .context("compute L2 HMAC for get_order_status")?;

    let url = format!("{CLOB_API}{}", path);
    let resp = client
        .get(&url)
        .header("POLY_ADDRESS", format!("{:#x}", wallet.address))
        .header("POLY_SIGNATURE", l2_sig)
        .header("POLY_TIMESTAMP", timestamp.to_string())
        .header("POLY_API_KEY", &wallet.creds.api_key)
        .header("POLY_PASSPHRASE", &wallet.creds.passphrase)
        .send()
        .await
        .context("get order status request")?;

    if !resp.status().is_success() {
        let error_text = resp.text().await.unwrap_or_default();
        return Err(anyhow!("Get order status failed: {}", error_text));
    }

    let order: OpenOrder = resp.json().await.context("parse order status response")?;
    Ok(order)
}

// ── Submit multiple orders in a single batch via POST /orders ─────────────────
async fn place_batch_orders(
    client: &Client,
    wallet: &Arc<TradingWallet>,
    orders: Vec<CreateOrderRequest>,
) -> Result<Vec<BatchOrderResult>> {
    let body_str = serde_json::to_string(&orders).context("serialise batch orders")?;

    let timestamp = now_ms() / 1000;
    let l2_sig = l2_signature(&wallet.creds.secret, timestamp, "POST", "/orders", &body_str)
        .context("compute L2 HMAC for batch orders")?;

    let url = format!("{CLOB_API}/orders");
    let resp = client
        .post(&url)
        .header("Content-Type", "application/json")
        .header("POLY_ADDRESS", format!("{:#x}", wallet.address))
        .header("POLY_SIGNATURE", l2_sig)
        .header("POLY_TIMESTAMP", timestamp.to_string())
        .header("POLY_API_KEY", &wallet.creds.api_key)
        .header("POLY_PASSPHRASE", &wallet.creds.passphrase)
        .body(body_str)
        .send()
        .await
        .context("place batch orders")?;

    let resp_status = resp.status();
    let resp_body = resp.text().await.unwrap_or_default();

    if !resp_status.is_success() {
        return Err(anyhow!("Batch order placement failed ({}): {}", resp_status, resp_body));
    }

    eprintln!("Batch raw response: {}", resp_body);
    let results: Vec<BatchOrderResult> = serde_json::from_str(&resp_body)
        .context("parse batch order response")?;
    Ok(results)
}

fn write_candle_csv(state: &MarketState, asset_id: &str, candle: &Candle) -> Result<()> {
    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(CSV_PATH)
        .context("open candle csv")?;

    if file.metadata()?.len() == 0 {
        writeln!(
            file,
            "market_slug,condition_id,outcome,asset_id,window_start_ms,window_end_ms,high,low,last_price,last_update_ms"
        )?;
    }

    let outcome = state
        .asset_to_outcome
        .get(asset_id)
        .cloned()
        .unwrap_or_else(|| "unknown".to_string());

    writeln!(
        file,
        "{},{},{},{},{},{},{},{},{},{}",
        state.market_slug,
        state.condition_id,
        outcome,
        asset_id,
        candle.start_ms,
        candle.end_ms,
        candle.high,
        candle.low,
        candle.last_price,
        candle.last_update_ms
    )?;
    Ok(())
}

fn parse_price(raw: &str) -> Option<f64> {
    raw.parse::<f64>().ok()
}

// ── POL auto-top-up via SimpleSwap ───────────────────────────────────────────

/// Reads the native POL (gas token) balance via eth_getBalance.
async fn get_pol_balance(client: &Client, address: &Address) -> Result<f64> {
    let ankr_key = env::var(ANKR_API_KEY_ENV)
        .with_context(|| format!("Missing env var '{ANKR_API_KEY_ENV}'"))?;
    let rpc_url = format!("https://rpc.ankr.com/polygon/{}", ankr_key.trim());

    let body = json!({
        "jsonrpc": "2.0",
        "method": "eth_getBalance",
        "params": [format!("{:#x}", address), "latest"],
        "id": 1
    });
    let resp: Value = client
        .post(&rpc_url)
        .json(&body)
        .send()
        .await
        .context("eth_getBalance")?
        .json()
        .await
        .context("parse eth_getBalance")?;

    if let Some(err) = resp.get("error") {
        return Err(anyhow!("eth_getBalance error: {err}"));
    }
    let hex = resp["result"]
        .as_str()
        .unwrap_or("0x0")
        .trim_start_matches("0x");
    let raw = u128::from_str_radix(hex, 16).unwrap_or(0);
    Ok(raw as f64 / 1e18) // POL has 18 decimals
}

/// POST /v3/exchanges — creates a floating-rate swap on SimpleSwap.
/// Swaps USDC.e (Polygon) for POL and sends it to `recipient`.
/// Returns the exchange object which contains the deposit address.
async fn create_simpleswap_exchange(
    client: &Client,
    amount_usdc: f64,
    recipient: &str,
) -> Result<SimpleSwapExchange> {
    let api_key = env::var(SIMPLESWAP_API_KEY_ENV)
        .with_context(|| format!("Missing '{SIMPLESWAP_API_KEY_ENV}' in .env"))?;

    let payload = json!({
        "tickerFrom":           "usdcpoly",   // USDC.e on Polygon
        "networkFrom":          "polygon",
        "tickerTo":             "pol",         // Polygon gas token (POL/MATIC)
        "networkTo":            "polygon",
        "amount":               format!("{:.6}", amount_usdc),
        "fixed":                false,
        "reverse":              false,
        "customFee":            null,
        "addressTo":            recipient,     // send POL here
        "extraIdTo":            "",
        "userRefundAddress":    recipient,     // refund USDC.e here if swap fails
        "userRefundExtraId":    "",
        "rateId":               ""
    });

    let resp = client
        .post("https://api.simpleswap.io/v3/exchanges")
        .header("x-api-key", api_key.trim())
        .header("Accept", "application/json")
        .json(&payload)
        .send()
        .await
        .context("SimpleSwap POST /v3/exchanges")?;

    let data: Value = resp.json().await.context("parse SimpleSwap response")?;

    // v3 wraps the payload in a "result" key
    let obj = data.get("result").unwrap_or(&data);

    if let Some(err) = data.get("error").or_else(|| data.get("message")) {
        return Err(anyhow!("SimpleSwap API error: {err}"));
    }

    Ok(SimpleSwapExchange {
        public_id: obj["publicId"].as_str().unwrap_or("").to_string(),
        address_from: obj["addressFrom"].as_str().unwrap_or("").to_string(),
        amount_from: obj["amountFrom"].as_str().unwrap_or("").to_string(),
        status: obj["status"].as_str().unwrap_or("").to_string(),
    })
}

/// Sends `amount_usdc` USDC.e (6-decimal ERC-20) to `to_address` on Polygon.
/// selector: transfer(address,uint256) = 0xa9059cbb
async fn send_usdc_transfer(
    client: &Client,
    wallet: &TradingWallet,
    to_address: &str,
    amount_usdc: f64,
) -> Result<String> {
    let ankr_key = env::var(ANKR_API_KEY_ENV)
        .with_context(|| format!("Missing env var '{ANKR_API_KEY_ENV}'"))?;
    let rpc_url = format!("https://rpc.ankr.com/polygon/{}", ankr_key.trim());

    // Nonce
    let nonce_body = json!({
        "jsonrpc": "2.0", "method": "eth_getTransactionCount",
        "params": [format!("{:#x}", wallet.address), "latest"], "id": 1
    });
    let nonce_resp: Value = client
        .post(&rpc_url)
        .json(&nonce_body)
        .send()
        .await
        .context("get nonce for USDC transfer")?
        .json()
        .await?;
    let nonce = nonce_resp["result"]
        .as_str()
        .and_then(|s| u64::from_str_radix(s.trim_start_matches("0x"), 16).ok())
        .ok_or_else(|| anyhow!("bad nonce: {nonce_resp}"))?;

    // Gas price
    let gas_body = json!({"jsonrpc":"2.0","method":"eth_gasPrice","params":[],"id":1});
    let gas_resp: Value = client
        .post(&rpc_url)
        .json(&gas_body)
        .send()
        .await
        .context("get gas price")?
        .json()
        .await?;
    let gas_price = gas_resp["result"]
        .as_str()
        .and_then(|s| u128::from_str_radix(s.trim_start_matches("0x"), 16).ok())
        .ok_or_else(|| anyhow!("bad gas price: {gas_resp}"))?;

    // transfer(address,uint256) calldata
    let amount_raw = (amount_usdc * 1_000_000.0) as u64; // 6 decimals
    let to_hex = to_address.trim_start_matches("0x");
    let calldata_hex = format!("a9059cbb{:0>64}{:0>64x}", to_hex, amount_raw);
    let calldata_bytes = hex::decode(&calldata_hex).context("decode USDC transfer calldata")?;

    use ethers::types::transaction::eip2718::TypedTransaction;
    let tx = TypedTransaction::Legacy(ethers::types::TransactionRequest {
        from: Some(wallet.address),
        to: Some(USDC_E_POLYGON.parse::<Address>().unwrap().into()),
        nonce: Some(U256::from(nonce)),
        gas: Some(U256::from(80_000u64)),
        gas_price: Some(U256::from(gas_price * 3)), // 3× for fast inclusion
        data: Some(calldata_bytes.into()),
        value: Some(U256::zero()),
        chain_id: Some(U64::from(CHAIN_ID)),
        ..Default::default()
    });

    let sig = wallet
        .wallet
        .sign_transaction(&tx)
        .await
        .map_err(|e| anyhow!("sign USDC transfer: {e}"))?;
    let raw_tx = format!("0x{}", hex::encode(tx.rlp_signed(&sig)));

    let send_body = json!({
        "jsonrpc": "2.0", "method": "eth_sendRawTransaction",
        "params": [raw_tx], "id": 1
    });
    let send_resp: Value = client
        .post(&rpc_url)
        .json(&send_body)
        .send()
        .await
        .context("broadcast USDC transfer")?
        .json()
        .await?;

    if let Some(err) = send_resp.get("error") {
        return Err(anyhow!("USDC transfer tx failed: {err}"));
    }
    let tx_hash = send_resp["result"]
        .as_str()
        .ok_or_else(|| anyhow!("no tx hash in response: {send_resp}"))?
        .to_string();

    Ok(tx_hash)
}

/// Checks the POL (gas token) balance and, if below POL_LOW_THRESHOLD,
/// creates a SimpleSwap exchange and sends USDC.e to the deposit address.
/// SimpleSwap will then forward POL to our wallet asynchronously.
async fn check_and_top_up_pol(client: &Client, wallet: &Arc<TradingWallet>) -> Result<()> {
    // Skip silently if no API key configured
    if env::var(SIMPLESWAP_API_KEY_ENV)
        .map(|k| k.trim().is_empty())
        .unwrap_or(true)
    {
        return Ok(());
    }

    let pol = match get_pol_balance(client, &wallet.address).await {
        Ok(b) => b,
        Err(e) => {
            eprintln!("WARN: Could not check POL balance: {e:#}");
            return Ok(());
        }
    };

    if pol >= POL_LOW_THRESHOLD {
        return Ok(());
    }

    let recipient = format!("{:#x}", wallet.address);

    let exchange = match create_simpleswap_exchange(client, POL_TOP_UP_USDC, &recipient).await {
        Ok(e) => e,
        Err(e) => {
            eprintln!("WARN: SimpleSwap exchange creation failed: {e:#}");
            return Ok(());
        }
    };

    if exchange.address_from.is_empty() {
        eprintln!("WARN: SimpleSwap returned empty deposit address. Skipping top-up.");
        return Ok(());
    }

    match send_usdc_transfer(client, wallet, &exchange.address_from, POL_TOP_UP_USDC).await {
        Ok(_tx_hash) => {}
        Err(e) => {
            eprintln!("POL top-up USDC transfer failed: {e:#}");
        }
    }

    Ok(())
}

async fn send_error_alert(message: &str) -> Result<()> {
    if ERROR_DISCORD_WEBHOOK_URL.trim().is_empty() {
        return Ok(());
    }

    let client = Client::new();
    let payload = json!({ "content": message });
    client
        .post(ERROR_DISCORD_WEBHOOK_URL)
        .json(&payload)
        .send()
        .await
        .context("send error alert webhook")?;
    Ok(())
}

async fn send_discord_embed(embed: Value) -> Result<()> {
    if DISCORD_WEBHOOK_URL.trim().is_empty() {
        return Ok(());
    }

    let client = Client::new();
    let payload = json!({ "embeds": [embed] });
    client
        .post(DISCORD_WEBHOOK_URL)
        .json(&payload)
        .send()
        .await
        .context("send discord embed")?;
    Ok(())
}

fn parse_timestamp(value: Option<&Value>) -> Option<i64> {
    let v = value?;
    if let Some(s) = v.as_str() {
        s.parse::<i64>().ok()
    } else if let Some(n) = v.as_i64() {
        Some(n)
    } else {
        None
    }
}

fn now_ms() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_millis() as i64)
        .unwrap_or(0)
}
