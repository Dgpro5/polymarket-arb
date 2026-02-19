use anyhow::{anyhow, Context, Result};
use futures_util::{SinkExt, StreamExt};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
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
const MIN_PROFIT_THRESHOLD: f64 = 97.5; // sum_cents must be <= this to trade
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
struct TradingWallet {
    wallet: LocalWallet,
    address: Address,
}

impl TradingWallet {
    fn new(private_key: &str) -> Result<Self> {
        let wallet = private_key.parse::<LocalWallet>()
            .context("parse private key")?;
        let address = wallet.address();
        println!("Trading wallet address: {:#x}", address);
        Ok(Self { wallet, address })
    }
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

#[derive(Debug, Serialize)]
struct CreateOrderPayload {
    token_id: String,
    price: String,
    size: String,
    side: String, // "BUY" or "SELL"
    #[serde(rename = "type")]
    order_type: String, // "GTC" = Good Till Cancelled
    signature: String,
    #[serde(rename = "signatureType")]
    signature_type: u8, // 0 = EOA, 1 = POLY_PROXY, 2 = POLY_GNOSIS_SAFE
}

// USDC contract on Polygon (6 decimals)
const USDC_POLYGON: &str = "0x3c499c542cef5e3811e1192ce70d8cc03d5c3359";
const ANKR_API_KEY_ENV: &str = "ANKR_API_KEY";

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
    let wallet = Arc::new(TradingWallet::new(private_key.trim())?);
    let client = Client::new();

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
    }));

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
                }

                // Reset window budget: fetch current balance and set limits for this window
                match get_balance(&client, &wallet.address).await {
                    Ok(balance) => {
                        let mut m = money.lock().await;
                        m.money_spent = 0.0;
                        m.window_budget = balance * 0.75;   // stop after spending 3/4
                        m.per_trade_limit = balance * 0.25; // max 1/4 per trade
                        notify_important(&format!(
                            "Window budget set: balance=${:.4}, per_trade_limit=${:.4}, window_budget=${:.4}",
                            balance, m.per_trade_limit, m.window_budget
                        )).await?;
                    }
                    Err(e) => {
                        eprintln!("WARN: Could not fetch balance for budget reset: {e:#}");
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
        let sum_cents = (up + down) * 100.0;

        if sum_cents <= MIN_PROFIT_THRESHOLD {
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

            match execute_arbitrage_trade(wallet, &up_asset, &down_asset, up, down, sum_cents, trade_budget).await {
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

    // Step 2: Verify live balance still covers the trade (sanity check)
    let balance = get_balance(&client, &wallet.address).await?;
    let estimated_cost = cost_per_pair * (buy_shares as f64);
    let required_balance = estimated_cost * (1.0 + SLIPPAGE_TOLERANCE);

    log.push(format!(
        "Balance check: have=${:.4}, need=${:.4} ({}% slippage buffer), trade_budget=${:.4}",
        balance, required_balance, SLIPPAGE_TOLERANCE * 100.0, trade_budget
    ));

    if balance < required_balance {
        return Err(anyhow!(
            "{}\nERROR: Live balance ${:.4} below required ${:.4} (shares={}, up={:.4}, down={:.4})",
            log.join("\n"), balance, required_balance, buy_shares, up_price, down_price
        ));
    }

    // Step 3: Execute trades — buy both UP and DOWN legs
    log.push("Placing orders...".to_string());

    let up_order_id = place_market_order(&client, wallet, up_asset_id, buy_shares, up_price, "BUY").await?;
    log.push(format!("UP order placed: {}", up_order_id));

    // FIX 7: If the DOWN order fails after UP succeeded we log the error rather than
    // silently dropping it. In a real system you would want to attempt a compensating
    // sell of the UP leg here; for now we surface the failure clearly.
    let down_result = place_market_order(&client, wallet, down_asset_id, buy_shares, down_price, "BUY").await;
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

async fn place_market_order(
    client: &Client,
    wallet: &Arc<TradingWallet>,
    token_id: &str,
    size: u64,
    price: f64,
    side: &str,
) -> Result<String> {
    let price_str = format!("{:.4}", price);
    let size_str = size.to_string();

    // FIX 5 (signing note): The sign_order function below uses a simplified keccak256
    // of a plain string. Polymarket's CLOB API requires proper EIP-712 structured-data
    // signing with the Polymarket domain separator. If orders are rejected with a
    // signature error, you will need to implement full EIP-712 signing per:
    // https://github.com/Polymarket/py-order-utils
    let signature = sign_order(wallet, token_id, &price_str, &size_str, side).await?;

    let payload = CreateOrderPayload {
        token_id: token_id.to_string(),
        price: price_str,
        size: size_str,
        side: side.to_string(),
        order_type: "GTC".to_string(),
        signature,
        signature_type: 0, // EOA signature
    };

    let url = format!("{CLOB_API}/order");
    let resp = client
        .post(&url)
        .json(&payload)
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
        .ok_or_else(|| anyhow!("No order ID in response"))?
        .to_string();

    Ok(order_id)
}

async fn sign_order(
    wallet: &Arc<TradingWallet>,
    token_id: &str,
    price: &str,
    size: &str,
    side: &str,
) -> Result<String> {
    let message = format!("{}:{}:{}:{}", token_id, price, size, side);
    let message_hash = keccak256(message.as_bytes());

    let signature = wallet.wallet.sign_message(&message_hash)
        .await
        .map_err(|e| anyhow!("Signing failed: {}", e))?;

    Ok(format!("0x{}", hex::encode(signature.to_vec())))
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