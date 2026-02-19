use anyhow::{anyhow, Context, Result};
use base64::{engine::general_purpose::URL_SAFE as BASE64, Engine};
use futures_util::{SinkExt, StreamExt};
use hmac::{Hmac, Mac};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::Sha256;
use std::collections::HashMap;
use std::env;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::sync::{Arc, atomic::{AtomicI64, Ordering}};
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tokio::sync::Mutex;
use tokio_tungstenite::connect_async;
use tokio_tungstenite::tungstenite::Message;
use ethers::prelude::*;
use ethers::signers::{LocalWallet, Signer};
use ethers::utils::keccak256;

const GAMMA_API: &str = "https://gamma-api.polymarket.com";
const CLOB_API: &str = "https://clob.polymarket.com";
const CLOB_WS_URL: &str = "wss://ws-subscriptions-clob.polymarket.com/ws/market";
const CANDLE_MS: i64 = 5 * 60 * 1000;
const DATA_DIR: &str = "data";
const LATEST_PATH: &str = "data/btc_updown_5m_latest.json";
const CSV_PATH: &str = "data/btc_updown_5m_candles.csv";
const DISCORD_WEBHOOK_URL: &str = "https://discord.com/api/webhooks/1473284259363164211/4sgTuuoGlwS4OyJ5x6-QmpPA_Q1gvsIZB9EZrb9zWX6qyA0LMQklz3IupBfINPVnpsMZ";
const DETECTION_COOLDOWN_MS: i64 = 500;

const PRIVATE_KEY_ENV: &str = "PRIVATE_KEY";

// Trading parameters
// Profit threshold is computed dynamically from the live fee rate.
// Formula: sum_cents < 100.0 / (1.0 + fee_bps / 10000.0)
// This constant is a hard fallback only used if the fee fetch fails.
const MIN_PROFIT_THRESHOLD_FALLBACK: f64 = 90.0;
const SLIPPAGE_TOLERANCE: f64 = 0.02;   // 2% slippage tolerance

static LAST_DETECTION_MS: AtomicI64 = AtomicI64::new(0);

#[derive(Debug, Clone)]
struct Candle {
    start_ms: i64,
    end_ms: i64,
    high: f64,
    low: f64,
    last_price: f64,
    last_update_ms: i64,
}

impl Candle {
    fn new(start_ms: i64, price: f64, ts: i64) -> Self {
        Self {
            start_ms,
            end_ms: start_ms + CANDLE_MS,
            high: price,
            low: price,
            last_price: price,
            last_update_ms: ts,
        }
    }

    fn update(&mut self, price: f64, ts: i64) {
        if price > self.high {
            self.high = price;
        }
        if price < self.low {
            self.low = price;
        }
        self.last_price = price;
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
}

struct MoneyManager {
    money_spent: f64,
    total_buy_positions: i64,
    total_shares_bought: i64,
    // Budget for the current 5-minute window
    window_budget: f64,      // 3/4 of balance at window start — hard stop when reached
    per_trade_limit: f64,    // 1/4 of balance at window start — max spend per trade
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

// Wrapper sent to POST /order
#[derive(Debug, Serialize)]
struct CreateOrderRequest {
    order: PolymarketOrderStruct,
    owner: String,        // apiKey
    #[serde(rename = "orderType")]
    order_type: String,   // "GTC"
    #[serde(rename = "deferExec")]
    defer_exec: bool,     // false = execute immediately
}

// USDC contract on Polygon (6 decimals)
const USDC_POLYGON: &str = "0x3c499c542cef5e3811e1192ce70d8cc03d5c3359";
const ANKR_API_KEY_ENV: &str = "ANKR_API_KEY";

// Polymarket CTF Exchange on Polygon (non-neg-risk markets)
const CTF_EXCHANGE_ADDRESS: &str = "0x4bFb41d5B3570DeFd03C39a9A4D8dE6Bd8B8982E";
const CHAIN_ID: u64 = 137;
// Zero address — any counterparty can fill the order
const ZERO_ADDRESS: &str = "0x0000000000000000000000000000000000000000";

#[tokio::main]
async fn main() -> Result<()> {
    dotenvy::dotenv().ok();
    fs::create_dir_all(DATA_DIR).context("create data dir")?;

    // Reads PRIVATE_KEY from the .env file (loaded above via dotenvy::dotenv()).
    // Never hardcode this value — keep it in .env and add .env to .gitignore.
    let private_key = env::var(PRIVATE_KEY_ENV)
        .with_context(|| format!("Missing env var '{PRIVATE_KEY_ENV}' — add it to your .env file"))?;
    if private_key.trim().is_empty() {
        return Err(anyhow!("'{PRIVATE_KEY_ENV}' is set but empty in .env"));
    }

    let client = Client::new();

    // Parse the raw wallet so we can use it for L1 auth signing
    let wallet_signer = private_key.trim().parse::<LocalWallet>()
        .context("parse private key")?;
    let address = wallet_signer.address();
    println!("Trading wallet address: {:#x}", address);

    // L1 auth: sign an EIP-712 message with the private key to obtain API credentials
    notify_important("Obtaining Polymarket API credentials via L1 auth...").await?;
    let creds = get_or_create_api_creds(&wallet_signer, address, &client).await?;
    notify_important(&format!("API credentials ready. apiKey={}", creds.api_key)).await?;

    let wallet = Arc::new(TradingWallet { wallet: wallet_signer, address, creds });

    // Initialize money manager
    let money: Arc<Mutex<MoneyManager>> = Arc::new(Mutex::new(MoneyManager {
        money_spent: 0.0,
        total_buy_positions: 0,
        total_shares_bought: 0,
        window_budget: 0.0,
        per_trade_limit: 0.0,
    }));

    // Check initial balance — non-fatal so a bad endpoint doesn't block startup
    match get_balance(&client, &wallet.address).await {
        Ok(balance) => notify_important(&format!("Initial USDC balance: ${:.4}", balance)).await?,
        Err(e) => {
            eprintln!("WARN: Could not fetch initial balance: {e:#}");
            eprintln!("WARN: Bot will still run — balance is re-checked before each trade.");
        }
    }

    let market = discover_active_btc_5m_market(&client).await?;

    notify_important(&format!(
        "Active market: https://polymarket.com/event/{}",
        market.slug
    ))
    .await?;
    notify_important(&format!(
        "condition_id={}, asset_ids={:?}, outcomes={:?}",
        market.condition_id, market.asset_ids, market.outcomes
    ))
    .await?;

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
    }));

    // Background task: refresh fee rate every second without blocking the main loop
    let fee_task_state  = Arc::clone(&state);
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
                        if guard.fee_bps != new_fee {
                            let break_even = 100.0 / (1.0 + new_fee as f64 / 10000.0);
                            println!(
                                "Fee rate updated: {} -> {} bps. New profit threshold: {:.2}",
                                guard.fee_bps, new_fee, break_even
                            );
                            guard.fee_bps = new_fee;
                        }
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

    let mut backoff = 2u64;
    loop {
        match discover_active_btc_5m_market(&client).await {
            Ok(new_market) => {
                notify_important(&format!("Connecting to market: {}", new_market.slug)).await?;

                let now_secs = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap_or_default()
                    .as_secs() as i64;
                let secs_remaining = (new_market.end_ts - now_secs).max(1) as u64;
                notify_important(&format!("Window expires in {secs_remaining}s")).await?;

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
                }

                // Reset window budget: fetch current balance and set limits for this window
                match get_balance(&client, &wallet.address).await {
                    Ok(balance) => {
                        let mut m = money.lock().await;
                        m.money_spent = 0.0;
                        m.window_budget = balance * 0.75;
                        m.per_trade_limit = balance * 0.25;
                        notify_important(&format!(
                            "Window budget set: balance=${:.4}, per_trade_limit=${:.4}, window_budget=${:.4}",
                            balance, m.per_trade_limit, m.window_budget
                        )).await?;
                    }
                    Err(e) => {
                        eprintln!("WARN: Could not fetch balance for budget reset: {e:#}");
                    }
                }

                // Fetch live fee rate for this market and store it in state.
                // Uses the first asset_id — both UP and DOWN legs share the same fee.
                if let Some(first_asset) = new_market.asset_ids.first() {
                    match get_fee_rate(&client, first_asset).await {
                        Ok(fee_bps) => {
                            let mut guard = state.lock().await;
                            guard.fee_bps = fee_bps;
                            let break_even = 100.0 / (1.0 + fee_bps as f64 / 10000.0);
                            notify_important(&format!(
                                "Fee rate: {fee_bps} bps ({:.2}%). Profit threshold: sum_cents < {break_even:.2}",
                                fee_bps as f64 / 100.0
                            )).await?;
                        }
                        Err(e) => {
                            eprintln!("WARN: Could not fetch fee rate: {e:#}. Using fallback {MIN_PROFIT_THRESHOLD_FALLBACK}");
                        }
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
                                notify_important("Socket closed cleanly, re-discovering...").await?;
                                backoff = 2;
                                window_closed = true;
                                close_reason = "socket_closed";
                            }
                            Err(e) if e.to_string().contains("NO NEW ASSETS") => {
                                notify_important("Market ended (NO NEW ASSETS), re-discovering...").await?;
                                backoff = 2;
                                window_closed = true;
                                close_reason = "no_new_assets";
                            }
                            Err(e) => {
                                notify_important(&format!(
                                    "Socket error: {e:#}. Reconnecting in {backoff}s..."
                                ))
                                .await?;
                                tokio::time::sleep(Duration::from_secs(backoff)).await;
                                backoff = (backoff * 2).min(60);
                            }
                        }
                    }
                    _ = tokio::time::sleep(Duration::from_secs(secs_remaining)) => {
                        notify_important("Window expiry timer fired, waiting for boundary...").await?;
                        tokio::time::sleep(Duration::from_secs(3)).await;
                        notify_important("Switching to next market...").await?;
                        backoff = 2;
                        window_closed = true;
                        close_reason = "timer";
                    }
                }

                if window_closed {
                    send_money_snapshot(&money, close_reason).await?;
                }
            }
            Err(e) => {
                notify_important(&format!(
                    "Market discovery failed: {e:#}. Retrying in {backoff}s..."
                ))
                .await?;
                tokio::time::sleep(Duration::from_secs(backoff)).await;
                backoff = (backoff * 2).min(10);
            }
        }
    }
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
    println!("Computed active market slug: {slug} (window ends at Unix {end_ts})");

    let url = format!("{GAMMA_API}/markets?slug={slug}");
    let resp = client
        .get(&url)
        .send()
        .await
        .context("fetch btc-updown-5m market by slug")?;

    let data: Value = resp.json().await.context("parse market response")?;

    let market = data
        .as_array()
        .and_then(|arr| arr.first())
        .ok_or_else(|| {
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

    let asset_ids = parse_string_array(market.get("clobTokenIds"))
        .context("parse clobTokenIds")?;
    let outcomes = parse_string_array(market.get("outcomes"))
        .context("parse outcomes")?;

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
    let (ws_stream, _) = connect_async(CLOB_WS_URL).await.context("connect clob ws")?;
    let (mut write, mut read) = ws_stream.split();
    notify_important(&format!("Connected to CLOB WS {CLOB_WS_URL}")).await?;

    let subscribe_msg = json!({
        "type": "market",
        "assets_ids": asset_ids
    })
    .to_string();
    write
        .send(Message::Text(subscribe_msg))
        .await
        .context("send subscribe")?;

    notify_important(&format!("Subscribed to assets: {asset_ids:?}")).await?;

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
                } else {
                    eprintln!("Unrecognised WS message: {text}");
                }
            }
            Ok(Message::Ping(data)) => {
                write.send(Message::Pong(data)).await.ok();
            }
            Ok(Message::Close(_)) => break,
            Ok(_) => {}
            Err(e) => {
                notify_important(&format!("WS error: {e}")).await?;
                break;
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
            if let Some((asset_id, price, ts)) = parse_best_bid_ask(value) {
                update_outcome_price(state, money, wallet, &asset_id, price, ts).await?;
            }
        }
        "last_trade_price" => {
            if let Some((asset_id, price, ts)) = parse_last_trade(value) {
                update_outcome_price(state, money, wallet, &asset_id, price, ts).await?;
            }
        }
        "book" => {
            if let Some((asset_id, price, ts)) = parse_book_mid(value) {
                update_outcome_price(state, money, wallet, &asset_id, price, ts).await?;
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
                            update_outcome_price(state, money, wallet, &asset_id, price, ts).await?;
                        }
                    }
                }
            }
        }
        _ => {}
    }

    Ok(())
}

fn parse_best_bid_ask(value: &Value) -> Option<(String, f64, i64)> {
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

    Some((asset_id, price, ts))
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
    ts: i64,
) -> Result<()> {
    let start_ms = ts - (ts % CANDLE_MS);

    let mut guard = state.lock().await;
    if !guard.asset_to_outcome.contains_key(asset_id) {
        return Ok(());
    }

    let mut finished: Option<Candle> = None;

    match guard.candles.get_mut(asset_id) {
        Some(candle) if candle.start_ms == start_ms => {
            candle.update(price, ts);
        }
        Some(prev) => {
            finished = Some(prev.clone());
            guard
                .candles
                .insert(asset_id.to_string(), Candle::new(start_ms, price, ts));
        }
        None => {
            guard
                .candles
                .insert(asset_id.to_string(), Candle::new(start_ms, price, ts));
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
    let mut down_id = None;
    let mut down_price = None;
    let mut ts = None;

    for (asset_id, candle) in state.candles.iter() {
        let outcome = state
            .asset_to_outcome
            .get(asset_id)
            .cloned()
            .unwrap_or_else(|| "unknown".to_string());
        if outcome.eq_ignore_ascii_case("up") {
            up_id = Some(asset_id.clone());
            up_price = Some(candle.last_price);
            ts = Some(candle.last_update_ms);
        } else if outcome.eq_ignore_ascii_case("down") {
            down_id = Some(asset_id.clone());
            down_price = Some(candle.last_price);
            ts = Some(candle.last_update_ms);
        }
    }

    if let (Some(up), Some(down), Some(up_asset), Some(down_asset)) =
        (up_price, down_price, up_id, down_id)
    {
        // Round to tick size FIRST, then check profitability.
        // Raw prices may look profitable but round up past 100 cents.
        // e.g. up=0.475 -> 0.48, down=0.525 -> 0.53 => sum=101 cents => loss.
        let up   = (up   * 100.0).round() / 100.0;
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
            let now = now_ms();
            let last = LAST_DETECTION_MS.load(Ordering::Relaxed);
            if now - last < DETECTION_COOLDOWN_MS {
                return Ok(());
            }
            LAST_DETECTION_MS.store(now, Ordering::Relaxed);

            let message = format!(
                "Arbitrage opportunity: up={:.4}, down={:.4}, sum_cents={:.2}, ts={}",
                up, down, sum_cents, ts.unwrap_or(0)
            );
            notify_important(&message).await?;

            // Check window budget before trading
            {
                let m = money.lock().await;
                if m.window_budget == 0.0 {
                    println!("Budget not initialised yet, skipping trade.");
                    return Ok(());
                }
                if m.money_spent >= m.window_budget {
                    println!(
                        "Window budget exhausted (spent=${:.4} / limit=${:.4}), skipping trade.",
                        m.money_spent, m.window_budget
                    );
                    return Ok(());
                }
            }

            // Cap this trade at per_trade_limit, but never exceed remaining budget
            let trade_budget = {
                let m = money.lock().await;
                let remaining = m.window_budget - m.money_spent;
                m.per_trade_limit.min(remaining)
            };

            match execute_arbitrage_trade(wallet, &up_asset, &down_asset, up, down, sum_cents, trade_budget, fee_bps).await {
                Ok((trade_result, trade_log)) => {
                    let mut money = money.lock().await;
                    money.money_spent += trade_result.total_spent;
                    money.total_buy_positions += trade_result.shares_bought as i64;
                    money.total_shares_bought += (trade_result.shares_bought * 2) as i64;

                    let budget_remaining = money.window_budget - money.money_spent;
                    let trade_msg = format!(
                        "{}\n{}\nTRADE EXECUTED: {} shares each side @ up={:.4}, down={:.4}, total_spent=${:.2}, window_remaining=${:.4}",
                        message, trade_log, trade_result.shares_bought, up, down,
                        trade_result.total_spent, budget_remaining
                    );
                    send_discord_webhook(&trade_msg).await?;
                }
                Err(e) => {
                    let error_msg = format!("{}\nTRADE FAILED: {:#}", message, e);
                    eprintln!("{}", error_msg);
                    send_discord_webhook(&error_msg).await?;
                }
            }
        } else {
            println!(
                "Price update: up={:.4}, down={:.4}, sum_cents={:.2}, ts={}",
                up, down, sum_cents, ts.unwrap_or(0)
            );
        }
    }

    Ok(())
}

#[derive(Debug)]
struct TradeResult {
    shares_bought: u64,
    total_spent: f64,
}

async fn execute_arbitrage_trade(
    wallet: &Arc<TradingWallet>,
    up_asset_id: &str,
    down_asset_id: &str,
    up_price: f64,
    down_price: f64,
    sum_cents: f64,
    trade_budget: f64, // max USDC to spend on this single trade (1/4 of window balance)
    fee_bps: u64,      // maker fee in basis points, fetched live per market
) -> Result<(TradeResult, String)> {
    let client = Client::new();
    let mut log: Vec<String> = Vec::new();
    log.push(format!(
        "Trade attempt details: up_asset={}, down_asset={}, up={:.4}, down={:.4}, sum_cents={:.2}",
        up_asset_id, down_asset_id, up_price, down_price, sum_cents
    ));

    // Step 1: Get order books for both assets
    log.push("Fetching order books...".to_string());
    let up_book = get_order_book(&client, up_asset_id).await?;
    let down_book = get_order_book(&client, down_asset_id).await?;

    let up_total_size = calculate_total_size(&up_book.asks)?;
    let down_total_size = calculate_total_size(&down_book.asks)?;

    // Max shares fillable from the order book (both legs must match)
    let liquidity_shares = (up_total_size.min(down_total_size) * 0.8).floor();

    // Max shares affordable within the trade_budget (cost = (up+down) per share pair)
    let cost_per_pair = up_price + down_price;
    let budget_shares = (trade_budget / cost_per_pair).floor();

    // Use the smaller of the two so we never exceed budget or liquidity
    let buy_shares = liquidity_shares.min(budget_shares) as u64;

    log.push(format!(
        "Order book analysis: up_depth={:.2}, down_depth={:.2}, budget=${:.4}, cost_per_pair={:.4}, buying {} shares each side",
        up_total_size, down_total_size, trade_budget, cost_per_pair, buy_shares
    ));

    if buy_shares == 0 {
        return Err(anyhow!(
            "{}\nERROR: Zero shares — liquidity={:.2} or budget=${:.4} too small for cost_per_pair={:.4}",
            log.join("\n"), liquidity_shares, trade_budget, cost_per_pair
        ));
    }

    // Budget was already validated before calling this function (window_budget check).
    // No extra RPC balance call needed here — it would cost ~300ms in the hot path.
    let estimated_cost = cost_per_pair * (buy_shares as f64);

    // Step 2: Execute trades — buy both UP and DOWN legs
    log.push("Placing orders...".to_string());

    let up_order_id = place_market_order(&client, wallet, up_asset_id, buy_shares, up_price, "BUY", fee_bps).await?;
    log.push(format!("UP order placed: {}", up_order_id));

    // FIX 7: If the DOWN order fails after UP succeeded we log the error rather than
    // silently dropping it. In a real system you would want to attempt a compensating
    // sell of the UP leg here; for now we surface the failure clearly.
    let down_result = place_market_order(&client, wallet, down_asset_id, buy_shares, down_price, "BUY", fee_bps).await;
    match down_result {
        Ok(down_order_id) => {
            log.push(format!("DOWN order placed: {}", down_order_id));
        }
        Err(e) => {
            let msg = format!(
                "UP order {} succeeded but DOWN order FAILED: {:#}. Manual intervention required to balance position.",
                up_order_id, e
            );
            log.push(msg.clone());
            // Still propagate the error so the caller logs it to Discord
            return Err(anyhow!("{}\n{}", log.join("\n"), e));
        }
    }

    let total_spent = estimated_cost;

    Ok((
        TradeResult {
            shares_bought: buy_shares,
            total_spent,
        },
        log.join("\n"),
    ))
}

async fn get_fee_rate(client: &Client, token_id: &str) -> Result<u64> {
    let url = format!("{CLOB_API}/markets/fee-rate?token_id={token_id}");
    let resp = client
        .get(&url)
        .send()
        .await
        .context("fetch fee rate")?;

    let raw = resp.text().await.context("read fee rate response")?;
    let parsed: Value = serde_json::from_str(&raw)
        .with_context(|| format!("parse fee rate JSON: {raw}"))?;

    let fee = parsed
        .get("base_fee")
        .and_then(|v| v.as_u64())
        .ok_or_else(|| anyhow!("missing base_fee in fee rate response: {raw}"))?;

    Ok(fee)
}

async fn get_order_book(client: &Client, token_id: &str) -> Result<OrderBook> {
    let url = format!("{CLOB_API}/book?token_id={}", token_id);
    let resp = client
        .get(&url)
        .send()
        .await
        .context("fetch order book")?;

    let book: OrderBook = resp.json().await.context("parse order book")?;
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

async fn get_balance(client: &Client, address: &Address) -> Result<f64> {
    // Call USDC balanceOf(address) via raw eth_call on Ankr's Polygon RPC.
    // Reads ANKR_API_KEY from the .env file.
    let ankr_key = env::var(ANKR_API_KEY_ENV)
        .with_context(|| format!("Missing env var '{ANKR_API_KEY_ENV}' — add it to your .env file"))?;
    let ankr_key = ankr_key.trim().to_string();
    let masked_key = format!("{}...{}", &ankr_key[..6], &ankr_key[ankr_key.len()-4..]);
    println!("Using Ankr RPC: https://rpc.ankr.com/polygon/{masked_key}");
    let rpc_url = format!("https://rpc.ankr.com/polygon/{}", ankr_key);

    let addr_hex = format!("{:x}", address); // 40 hex chars, no 0x prefix
    // ABI-encode: 12 zero-bytes padding + 20-byte address = 32-byte word
    let calldata = format!("0x70a08231{:0>64}", addr_hex);

    let body = json!({
        "jsonrpc": "2.0",
        "method": "eth_call",
        "params": [
            { "to": USDC_POLYGON, "data": calldata },
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
    let parsed: Value = serde_json::from_str(&raw)
        .with_context(|| format!("parse eth_call JSON: {raw}"))?;

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

// ── L1 EIP-712 Auth ─────────────────────────────────────────────────────────
//
// Signs the ClobAuth struct using ethers-rs TypedData — matches the official
// TypeScript client exactly (same domain, same field encoding).
async fn l1_auth_signature(wallet: &LocalWallet, address: Address, timestamp: i64, nonce: u64) -> Result<String> {
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
    })).context("build ClobAuth TypedData")?;

    let sig = wallet.sign_typed_data(&typed_data).await
        .map_err(|e| anyhow!("sign_typed_data (L1 ClobAuth) failed: {e}"))?;

    Ok(format!("0x{}", hex::encode(sig.to_vec())))
}

// ── L2 HMAC-SHA256 Auth ───────────────────────────────────────────────────────
//
// Produces the POLY_SIGNATURE header for authenticated CLOB API calls.
// message = timestamp + METHOD + path + body
fn l2_signature(secret: &str, timestamp: i64, method: &str, path: &str, body: &str) -> Result<String> {
    let message = format!("{}{}{}{}", timestamp, method.to_uppercase(), path, body);
    let secret_bytes = BASE64.decode(secret).context("decode L2 secret (not valid base64)")?;
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
        .header("POLY_ADDRESS",   &address_str)
        .header("POLY_SIGNATURE", &signature)
        .header("POLY_TIMESTAMP", timestamp.to_string())
        .header("POLY_NONCE",     nonce.to_string())
        .send()
        .await
        .context("L1 auth GET /auth/derive-api-key")?;

    let derive_raw = derive_resp.text().await.context("read derive response")?;
    println!("GET /auth/derive-api-key response: {derive_raw}");
    let derive_parsed: Value = serde_json::from_str(&derive_raw)
        .with_context(|| format!("parse derive JSON: {derive_raw}"))?;

    if let (Some(k), Some(s), Some(p)) = (
        derive_parsed.get("apiKey").and_then(|v| v.as_str()),
        derive_parsed.get("secret").and_then(|v| v.as_str()),
        derive_parsed.get("passphrase").and_then(|v| v.as_str()),
    ) {
        println!("Derived existing API credentials.");
        return Ok(ApiCredentials {
            api_key:    k.to_string(),
            secret:     s.to_string(),
            passphrase: p.to_string(),
        });
    }

    // ── Step 2: fall back to POST /api-key (creates new credentials) ────────
    // NOTE: If this returns "Could not create api key", your wallet has not been
    // registered on Polymarket yet. Visit https://polymarket.com, connect wallet
    // 0x5f747b55957ecff985faed31635df8c6fc3677b7, and accept the Terms of Service.
    // After that, restart the bot and credentials will be created automatically.
    println!("No existing credentials found, attempting to create new ones via POST /auth/api-key...");

    // Re-sign with a fresh timestamp for the second request
    let timestamp2 = now_ms() / 1000;
    let signature2 = l1_auth_signature(wallet, address, timestamp2, nonce).await?;

    let create_resp = client
        .post(format!("{CLOB_API}/auth/api-key"))
        .header("POLY_ADDRESS",   &address_str)
        .header("POLY_SIGNATURE", &signature2)
        .header("POLY_TIMESTAMP", timestamp2.to_string())
        .header("POLY_NONCE",     nonce.to_string())
        .send()
        .await
        .context("L1 auth POST /auth/api-key")?;

    let create_raw = create_resp.text().await.context("read create response")?;
    println!("POST /auth/api-key response: {create_raw}");
    let create_parsed: Value = serde_json::from_str(&create_raw)
        .with_context(|| format!("parse create JSON: {create_raw}"))?;

    let api_key = create_parsed.get("apiKey").and_then(|v| v.as_str())
        .ok_or_else(|| anyhow!(
            "Could not obtain API credentials.
             Server response: {create_raw}
             
             If you see \"Could not create api key\", your wallet is not registered.
             Fix: Go to https://polymarket.com, connect wallet {address_str}, accept ToS, then restart."
        ))?;
    let secret = create_parsed.get("secret").and_then(|v| v.as_str())
        .ok_or_else(|| anyhow!("No secret in create response: {create_raw}"))?;
    let passphrase = create_parsed.get("passphrase").and_then(|v| v.as_str())
        .ok_or_else(|| anyhow!("No passphrase in create response: {create_raw}"))?;

    Ok(ApiCredentials {
        api_key:    api_key.to_string(),
        secret:     secret.to_string(),
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
            "expiration":    "0",
            "nonce":         "0",
            "feeRateBps":    fee_bps.to_string(),
            "side":          side,
            "signatureType": 0u8
        }
    })).context("build Order TypedData")?;

    let sig = wallet.sign_typed_data(&typed_data).await
        .map_err(|e| anyhow!("sign_typed_data (Order) failed: {e}"))?;

    Ok(format!("0x{}", hex::encode(sig.to_vec())))
}

// ── Place a market order with full L2 auth + EIP-712 signed order ─────────────
async fn place_market_order(
    client: &Client,
    wallet: &Arc<TradingWallet>,
    token_id: &str,
    size: u64,
    price: f64,
    side: &str,
    fee_bps: u64,
) -> Result<String> {
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

    // Use current timestamp as salt for uniqueness
    let salt = now_ms() as u64;

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
    ).await?;

    // Build the order struct — field types and values match the documented payload exactly
    let order = PolymarketOrderStruct {
        salt,                                          // u64 integer, not a string
        maker: format!("{:#x}", wallet.address),
        signer: format!("{:#x}", wallet.address),
        taker: ZERO_ADDRESS.to_string(),
        token_id: token_id.to_string(),
        maker_amount: maker_amount.to_string(),
        taker_amount: taker_amount.to_string(),
        side: side.to_string(),                        // "BUY" or "SELL" string, not 0/1
        expiration: "0".to_string(),
        nonce: "0".to_string(),
        fee_rate_bps: fee_bps.to_string(), // live fee rate fetched from /markets/fee-rate
        signature,
        signature_type: 0,                             // 0 = EOA
    };

    let request_body = CreateOrderRequest {
        order,
        owner: wallet.creds.api_key.clone(),
        order_type: "GTC".to_string(),
        defer_exec: false,
    };

    let body_str = serde_json::to_string(&request_body).context("serialise order request")?;
    println!("POST /order body: {body_str}");

    // L2 HMAC authentication headers
    let timestamp = now_ms() / 1000;
    let l2_sig = l2_signature(&wallet.creds.secret, timestamp, "POST", "/order", &body_str)
        .context("compute L2 HMAC signature")?;

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
        .context("place order")?;

    if !resp.status().is_success() {
        let error_text = resp.text().await.unwrap_or_default();
        return Err(anyhow!("Order placement failed: {}", error_text));
    }

    let result: Value = resp.json().await.context("parse order response")?;
    let order_id = result
        .get("orderID")
        .or_else(|| result.get("order_id"))
        .and_then(|v| v.as_str())
        .ok_or_else(|| anyhow!("No order ID in response: {}", result))?
        .to_string();

    Ok(order_id)
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

async fn send_discord_webhook(message: &str) -> Result<()> {
    if DISCORD_WEBHOOK_URL.trim().is_empty() {
        return Ok(());
    }

    let client = Client::new();
    let payload = json!({ "content": message });
    client
        .post(DISCORD_WEBHOOK_URL)
        .json(&payload)
        .send()
        .await
        .context("send discord webhook")?;
    Ok(())
}

async fn notify_important(message: &str) -> Result<()> {
    println!("{message}");
    if let Err(e) = send_discord_webhook(message).await {
        eprintln!("Discord webhook send failed: {e:#}");
    }
    Ok(())
}

async fn send_money_snapshot(money: &Arc<Mutex<MoneyManager>>, reason: &str) -> Result<()> {
    let snapshot = {
        let money = money.lock().await;
        let gross_payout = money.total_shares_bought as f64 * 1.0;
        let net_pnl = gross_payout - money.money_spent;
        let budget_used_pct = if money.window_budget > 0.0 {
            (money.money_spent / money.window_budget) * 100.0
        } else {
            0.0
        };
        format!(
            "Window closed ({reason}).\n             money_spent=${:.4} ({:.1}% of ${:.4} window budget)\n             per_trade_limit=${:.4} | trades={} | total_shares={}\n             estimated_gross_payout=${:.4} | estimated_net_pnl=${:.4}\n             (assumes all positions resolve at $1.00)",
            money.money_spent,
            budget_used_pct,
            money.window_budget,
            money.per_trade_limit,
            money.total_buy_positions,
            money.total_shares_bought,
            gross_payout,
            net_pnl,
        )
    };
    send_discord_webhook(&snapshot).await?;
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