use anyhow::{anyhow, Context, Result};
use futures_util::{SinkExt, StreamExt};
use reqwest::Client;
use serde_json::{json, Value};
use std::collections::HashMap;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::sync::Arc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tokio::sync::Mutex;
use tokio_tungstenite::connect_async;
use tokio_tungstenite::tungstenite::Message;

const GAMMA_API: &str = "https://gamma-api.polymarket.com";
const CLOB_WS_URL: &str = "wss://ws-subscriptions-clob.polymarket.com/ws/market";
const CANDLE_MS: i64 = 5 * 60 * 1000;
const DATA_DIR: &str = "data";
const LATEST_PATH: &str = "data/btc_updown_5m_latest.json";
const CSV_PATH: &str = "data/btc_updown_5m_candles.csv";

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

#[tokio::main]
async fn main() -> Result<()> {
    fs::create_dir_all(DATA_DIR).context("create data dir")?;

    let client = Client::new();

    // Discover the currently active BTC 5-minute market dynamically.
    // These markets expire every 5 minutes, so we must never hardcode the slug.
    let market = discover_active_btc_5m_market(&client).await?;

    println!(
        "Active market: https://polymarket.com/event/{}",
        market.slug
    );
    println!(
        "condition_id={}, asset_ids={:?}, outcomes={:?}",
        market.condition_id, market.asset_ids, market.outcomes
    );

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

    // Background task: write latest snapshot to disk every second.
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

    // Main loop: reconnect on socket errors. When the market expires mid-session
    // (signalled by NO NEW ASSETS), re-discover the new active market.
    let mut current_market = market;
    let mut backoff = 2u64;
    loop {
        let result = run_socket(Arc::clone(&state), &current_market.asset_ids).await;
        match result {
            Err(e) if e.to_string().contains("NO NEW ASSETS") => {
                eprintln!("Market expired. Discovering next active market in {backoff}s...");
                tokio::time::sleep(Duration::from_secs(backoff)).await;
                match discover_active_btc_5m_market(&client).await {
                    Ok(new_market) => {
                        println!("Switched to new market: {}", new_market.slug);
                        // Update shared state with new market info.
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
                        drop(guard);
                        current_market = new_market;
                        backoff = 2;
                    }
                    Err(e) => {
                        eprintln!("Failed to discover new market: {e:#}. Retrying in {backoff}s...");
                        backoff = (backoff * 2).min(60);
                    }
                }
            }
            Err(err) => {
                eprintln!("Socket error: {err:#}. Reconnecting in {backoff}s...");
                tokio::time::sleep(Duration::from_secs(backoff)).await;
                backoff = (backoff * 2).min(60);
            }
            Ok(_) => {
                backoff = 2;
            }
        }
    }
}

/// Finds the currently active BTC up/down 5-minute market by querying the
/// Gamma API, then picking the one whose expiry is soonest but still future.
async fn discover_active_btc_5m_market(client: &Client) -> Result<MarketInfo> {
    println!("Discovering active BTC 5-minute market...");

    let url = format!(
        "{GAMMA_API}/markets?slug_contains=btc-updown-5m&active=true&closed=false&limit=20"
    );

    let resp = client
        .get(&url)
        .send()
        .await
        .context("fetch active btc-updown-5m markets")?;

    let data: Value = resp
        .json()
        .await
        .context("parse active markets response")?;

    let markets = data
        .as_array()
        .ok_or_else(|| anyhow!("expected array from gamma API"))?;

    if markets.is_empty() {
        return discover_active_btc_5m_market_fallback(client).await;
    }

    println!("Found {} active candidate market(s)", markets.len());

    let now = now_ms();
    // Pick the market that expires soonest but hasn't expired yet.
    // If none are in the future, pick the one with the largest (most recent) expiry.
    let mut best: Option<(i64, &Value)> = None;

    for market in markets.iter() {
        let slug = market
            .get("slug")
            .and_then(|v| v.as_str())
            .unwrap_or_default();

        // The slug format is: btc-updown-5m-<unix_seconds>
        let expiry_ms = slug
            .rsplit('-')
            .next()
            .and_then(|s| s.parse::<i64>().ok())
            .map(|secs| secs * 1000)
            .unwrap_or(0);

        let is_future = expiry_ms > now;
        println!("  Candidate slug={slug}, expiry_ms={expiry_ms}, is_future={is_future}");

        // Score: future markets get their expiry as score (prefer sooner),
        // expired markets get 0.
        let score = if is_future { expiry_ms } else { 0 };
        let is_better = match best {
            None => true,
            Some((prev_score, _)) => {
                // Prefer any future over expired, then prefer sooner future.
                (score > 0 && prev_score == 0) || (score > 0 && score < prev_score)
            }
        };
        if is_better {
            best = Some((score, market));
        }
    }

    let chosen = best
        .map(|(_, m)| m)
        .ok_or_else(|| anyhow!("no suitable active btc-updown-5m market found"))?;

    let slug = chosen
        .get("slug")
        .and_then(|v| v.as_str())
        .unwrap_or_default()
        .to_string();

    println!("Selected market slug: {slug}");
    let mut info = parse_market_info(chosen)?;
    info.slug = slug;
    Ok(info)
}

/// Fallback discovery when active=true filter returns nothing.
/// Fetches all btc-updown-5m markets and picks the one closest to now.
async fn discover_active_btc_5m_market_fallback(client: &Client) -> Result<MarketInfo> {
    println!("Trying fallback market discovery (no active filter)...");
    let url = format!("{GAMMA_API}/markets?slug_contains=btc-updown-5m&limit=20");
    let resp = client
        .get(&url)
        .send()
        .await
        .context("fetch btc-updown-5m markets (fallback)")?;
    let data: Value = resp.json().await.context("parse fallback markets response")?;
    let markets = data
        .as_array()
        .ok_or_else(|| anyhow!("expected array from gamma API (fallback)"))?;

    if markets.is_empty() {
        return Err(anyhow!(
            "No btc-updown-5m markets found at all. \
             Check https://gamma-api.polymarket.com/markets?slug_contains=btc-updown-5m \
             to verify the naming is still correct."
        ));
    }

    let now = now_ms();
    // Pick the market whose expiry timestamp (from slug) is closest to now.
    let mut best: Option<(i64, &Value)> = None;
    for market in markets.iter() {
        let slug = market
            .get("slug")
            .and_then(|v| v.as_str())
            .unwrap_or_default();
        let expiry_ms = slug
            .rsplit('-')
            .next()
            .and_then(|s| s.parse::<i64>().ok())
            .map(|secs| secs * 1000)
            .unwrap_or(0);

        let diff = (expiry_ms - now).abs();
        match best {
            None => best = Some((diff, market)),
            Some((prev_diff, _)) if diff < prev_diff => best = Some((diff, market)),
            _ => {}
        }
    }

    let chosen = best
        .map(|(_, m)| m)
        .ok_or_else(|| anyhow!("no market found in fallback"))?;

    let slug = chosen
        .get("slug")
        .and_then(|v| v.as_str())
        .unwrap_or_default()
        .to_string();

    println!("Fallback selected slug: {slug}");
    let mut info = parse_market_info(chosen)?;
    info.slug = slug;
    Ok(info)
}

async fn run_socket(state: Arc<Mutex<MarketState>>, asset_ids: &[String]) -> Result<()> {
    let (ws_stream, _) = connect_async(CLOB_WS_URL).await.context("connect clob ws")?;
    let (mut write, mut read) = ws_stream.split();
    println!("Connected to CLOB WS {CLOB_WS_URL}");

    // Send ONE subscription message in the correct Polymarket CLOB format.
    let subscribe_msg = json!({
        "type": "market",
        "assets_ids": asset_ids
    })
    .to_string();
    write
        .send(Message::Text(subscribe_msg))
        .await
        .context("send subscribe")?;

    println!("Subscribed to assets: {asset_ids:?}");

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
                    handle_clob_message(&state, &value).await?;
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
                eprintln!("WS error: {e}");
                break;
            }
        }
    }

    Ok(())
}

async fn handle_clob_message(state: &Arc<Mutex<MarketState>>, value: &Value) -> Result<()> {
    if let Some(arr) = value.as_array() {
        for item in arr {
            handle_clob_message_single(state, item).await?;
        }
        return Ok(());
    }

    if let Some(data) = value.get("data") {
        if let Some(arr) = data.as_array() {
            for item in arr {
                handle_clob_message_single(state, item).await?;
            }
            return Ok(());
        }
        if data.is_object() {
            return handle_clob_message_single(state, data).await;
        }
    }

    handle_clob_message_single(state, value).await
}

async fn handle_clob_message_single(
    state: &Arc<Mutex<MarketState>>,
    value: &Value,
) -> Result<()> {
    let Some(event_type) = value.get("event_type").and_then(|v| v.as_str()) else {
        return Ok(());
    };

    match event_type {
        "best_bid_ask" => {
            if let Some((asset_id, price, ts)) = parse_best_bid_ask(value) {
                update_outcome_price(state, &asset_id, price, ts).await?;
            }
        }
        "last_trade_price" => {
            if let Some((asset_id, price, ts)) = parse_last_trade(value) {
                update_outcome_price(state, &asset_id, price, ts).await?;
            }
        }
        "book" => {
            if let Some((asset_id, price, ts)) = parse_book_mid(value) {
                update_outcome_price(state, &asset_id, price, ts).await?;
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
                            update_outcome_price(state, &asset_id, price, ts).await?;
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

    print_up_down(&guard);
    Ok(())
}

fn print_up_down(state: &MarketState) {
    let mut up = None;
    let mut down = None;
    let mut ts = None;

    for (asset_id, candle) in state.candles.iter() {
        let outcome = state
            .asset_to_outcome
            .get(asset_id)
            .cloned()
            .unwrap_or_else(|| "unknown".to_string());
        if outcome.eq_ignore_ascii_case("up") {
            up = Some(candle.last_price);
            ts = Some(candle.last_update_ms);
        } else if outcome.eq_ignore_ascii_case("down") {
            down = Some(candle.last_price);
            ts = Some(candle.last_update_ms);
        }
    }

    if let (Some(up), Some(down)) = (up, down) {
        let sum_cents = (up + down) * 100.0;
        if sum_cents <= 97.5 {
            println!(
                "Arbitrage opportunity: up={:.4}, down={:.4}, sum_cents={:.2}, ts={}",
                up,
                down,
                sum_cents,
                ts.unwrap_or(0)
            );
        } else {
            println!(
                "Price update: up={:.4}, down={:.4}, sum_cents={:.2}, ts={}",
                up,
                down,
                sum_cents,
                ts.unwrap_or(0)
            );
        }
    }
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