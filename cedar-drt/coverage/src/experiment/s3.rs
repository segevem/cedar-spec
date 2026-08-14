use std::path::Path;
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

/// PUT one object with EXPONENTIAL BACKOFF retry. S3 request-rate throttling
/// (503 SlowDown) and transient 500s are common when ~20 reps upload concurrently
/// from a c7i.48xlarge; the previous best-effort `let _ = ...send().await` silently
/// dropped those, so the corpus came out far smaller than the throughput count.
///
/// Retries up to `MAX_ATTEMPTS` with backoff 50ms, 100ms, 200ms, ... capped at 8s
/// (a deterministic per-key stagger avoids thundering-herd re-tries without needing
/// a RNG). Returns `Ok(())` only when the PUT is durably accepted; `Err` after the
/// budget is exhausted so the caller can count/hard-fail rather than silently lose it.
async fn put_with_retry(
    client: &aws_sdk_s3::Client,
    bucket: &str,
    key: &str,
    data: Vec<u8>,
) -> Result<(), String> {
    const MAX_ATTEMPTS: u32 = 12;
    // Deterministic 0..64ms stagger from the key so concurrent reps don't all
    // re-fire on the same schedule (no RNG needed, reproducible).
    let stagger = (key.bytes().fold(0u64, |a, b| a.wrapping_mul(31).wrapping_add(b as u64)) % 64) as u64;
    let mut last_err = String::new();
    for attempt in 0..MAX_ATTEMPTS {
        let body = aws_sdk_s3::primitives::ByteStream::from(data.clone());
        match client
            .put_object()
            .bucket(bucket)
            .key(key)
            .body(body)
            .send()
            .await
        {
            Ok(_) => return Ok(()),
            Err(e) => {
                last_err = format!("{e:?}");
                // backoff: 50ms * 2^attempt, capped at 8s, plus per-key stagger.
                let backoff = (50u64 << attempt.min(8)).min(8000) + stagger;
                tokio::time::sleep(Duration::from_millis(backoff)).await;
            }
        }
    }
    Err(format!(
        "PUT {key} failed after {MAX_ATTEMPTS} attempts: {last_err}"
    ))
}

/// Upload a directory tree to S3 under the given prefix.
/// Requires the `s3` feature and valid AWS credentials in the environment.
pub async fn upload_directory(
    client: &aws_sdk_s3::Client,
    bucket: &str,
    prefix: &str,
    local_dir: &Path,
) -> Result<u64, Box<dyn std::error::Error>> {
    let mut uploaded = 0u64;

    for entry in walkdir(local_dir)? {
        let relative = entry.strip_prefix(local_dir)?;
        let key = format!("{}/{}", prefix, relative.display());
        let body = aws_sdk_s3::primitives::ByteStream::from_path(&entry).await?;

        client
            .put_object()
            .bucket(bucket)
            .key(&key)
            .body(body)
            .send()
            .await?;

        uploaded += 1;
    }

    Ok(uploaded)
}

/// Download all objects under a prefix to a local directory.
pub async fn download_directory(
    client: &aws_sdk_s3::Client,
    bucket: &str,
    prefix: &str,
    local_dir: &Path,
) -> Result<u64, Box<dyn std::error::Error>> {
    std::fs::create_dir_all(local_dir)?;
    let mut downloaded = 0u64;

    let mut paginator = client
        .list_objects_v2()
        .bucket(bucket)
        .prefix(prefix)
        .into_paginator()
        .send();

    while let Some(page) = paginator.next().await {
        let page = page?;
        for obj in page.contents() {
            let key = obj.key().unwrap_or_default();
            let relative = key.strip_prefix(prefix).unwrap_or(key).trim_start_matches('/');
            if relative.is_empty() {
                continue;
            }
            let local_path = local_dir.join(relative);
            if let Some(parent) = local_path.parent() {
                std::fs::create_dir_all(parent)?;
            }

            let resp = client.get_object().bucket(bucket).key(key).send().await?;
            let bytes = resp.body.collect().await?.into_bytes();
            std::fs::write(&local_path, &bytes)?;
            downloaded += 1;
        }
    }

    Ok(downloaded)
}

/// Create an S3 client using the cedar-experiment profile.
/// This profile uses `credential_process` which auto-refreshes tokens via ada.
pub async fn make_client() -> aws_sdk_s3::Client {
    let config = aws_config::from_env()
        .profile_name("cedar-experiment")
        .region(aws_config::Region::new("us-east-1"))
        .load()
        .await;
    aws_sdk_s3::Client::new(&config)
}

/// Recursively list files in a directory.
fn walkdir(dir: &Path) -> std::io::Result<Vec<std::path::PathBuf>> {
    let mut files = Vec::new();
    if !dir.is_dir() {
        return Ok(files);
    }
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            files.extend(walkdir(&path)?);
        } else {
            files.push(path);
        }
    }
    Ok(files)
}

/// A background S3 uploader that accepts (key, bytes) messages and uploads
/// them asynchronously without blocking the caller. Drop to flush remaining uploads.
pub struct StreamingUploader {
    tx: Option<mpsc::SyncSender<UploadMsg>>,
    handle: Option<thread::JoinHandle<u64>>,
}

enum UploadMsg {
    Put { key: String, data: Vec<u8> },
    Shutdown,
}

impl StreamingUploader {
    pub fn new(bucket: String, prefix: String) -> Self {
        // Bounded: push() blocks when the upload thread is behind -> backpressure,
        // so buffered violation objects can't balloon memory.
        let (tx, rx) = mpsc::sync_channel::<UploadMsg>(256);

        let handle = thread::spawn(move || {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
                let client = make_client().await;
                let mut uploaded = 0u64;

                loop {
                    match rx.recv() {
                        Ok(UploadMsg::Put { key, data }) => {
                            let full_key = format!("{}/{}", prefix, key);
                            match put_with_retry(&client, &bucket, &full_key, data).await {
                                Ok(()) => uploaded += 1,
                                Err(e) => eprintln!(
                                    "FATAL: S3 PUT permanently failed for violation {}: {}",
                                    full_key, e
                                ),
                            }
                        }
                        Ok(UploadMsg::Shutdown) | Err(_) => break,
                    }
                }
                uploaded
            })
        });

        Self {
            tx: Some(tx),
            handle: Some(handle),
        }
    }

    /// Queue a file for upload. Non-blocking — returns immediately.
    pub fn put(&self, key: String, data: Vec<u8>) {
        if let Some(ref tx) = self.tx {
            let _ = tx.send(UploadMsg::Put { key, data });
        }
    }

    /// Flush remaining uploads and return the count of files uploaded.
    pub fn finish(mut self) -> u64 {
        if let Some(tx) = self.tx.take() {
            let _ = tx.send(UploadMsg::Shutdown);
        }
        self.handle
            .take()
            .and_then(|h| h.join().ok())
            .unwrap_or(0)
    }
}

impl Drop for StreamingUploader {
    fn drop(&mut self) {
        if let Some(tx) = self.tx.take() {
            let _ = tx.send(UploadMsg::Shutdown);
        }
        if let Some(h) = self.handle.take() {
            let _ = h.join();
        }
    }
}

/// Batch format: each input is stored as [4-byte LE length][payload].
/// A batch object contains many inputs concatenated in this format.
/// This allows efficient bulk upload (one S3 PUT per batch) and
/// sequential replay during analysis.

/// Encode a batch of inputs into a single byte vector.
/// Format: repeated [u32 LE length][payload bytes]
pub fn encode_batch(inputs: &[Vec<u8>]) -> Vec<u8> {
    let total_size: usize = inputs.iter().map(|i| 4 + i.len()).sum();
    let mut buf = Vec::with_capacity(total_size);
    for input in inputs {
        buf.extend_from_slice(&(input.len() as u32).to_le_bytes());
        buf.extend_from_slice(input);
    }
    buf
}

/// Decode a batch object back into individual inputs.
pub fn decode_batch(data: &[u8]) -> Vec<Vec<u8>> {
    let mut inputs = Vec::new();
    let mut pos = 0;
    while pos + 4 <= data.len() {
        let len = u32::from_le_bytes([data[pos], data[pos+1], data[pos+2], data[pos+3]]) as usize;
        pos += 4;
        if pos + len > data.len() {
            break;
        }
        inputs.push(data[pos..pos+len].to_vec());
        pos += len;
    }
    inputs
}

/// A batching S3 uploader. Accumulates inputs in memory and uploads them
/// as batch objects when the batch reaches `batch_size` inputs.
/// Each batch is a single S3 object named `batch_NNNNNN.bin`.
pub struct BatchUploader {
    tx: Option<mpsc::SyncSender<BatchMsg>>,
    handle: Option<thread::JoinHandle<u64>>,
    buffer: Vec<Vec<u8>>,
    batch_size: usize,
    batch_count: u64,
    input_count: u64,
}

enum BatchMsg {
    Upload { key: String, data: Vec<u8> },
    Shutdown,
}

impl BatchUploader {
    pub fn new(bucket: String, prefix: String, batch_size: usize) -> Self {
        // Bounded: push()/flush block when S3 uploads fall behind -> backpressure,
        // capping buffered corpus batches (~<=1MB each) at ~64MB/process.
        let (tx, rx) = mpsc::sync_channel::<BatchMsg>(64);

        let handle = thread::spawn(move || {
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
                let client = make_client().await;
                let mut uploaded = 0u64;

                loop {
                    match rx.recv() {
                        Ok(BatchMsg::Upload { key, data }) => {
                            let full_key = format!("{}/{}", prefix, key);
                            let data_len = data.len();
                            match put_with_retry(&client, &bucket, &full_key, data).await {
                                Ok(()) => uploaded += 1,
                                Err(e) => {
                                    // Exhausted retries: this is a HARD data-loss event, not a
                                    // routine throttle. Make it loud (and non-silent in the count).
                                    eprintln!(
                                        "FATAL: S3 PUT permanently failed for {} ({} bytes): {}",
                                        full_key, data_len, e
                                    );
                                }
                            }
                        }
                        Ok(BatchMsg::Shutdown) | Err(_) => break,
                    }
                }
                uploaded
            })
        });

        Self {
            tx: Some(tx),
            handle: Some(handle),
            buffer: Vec::with_capacity(batch_size),
            batch_size,
            batch_count: 0,
            input_count: 0,
        }
    }

    /// Add an input to the current batch. Flushes automatically when full.
    pub fn push(&mut self, data: Vec<u8>) {
        self.buffer.push(data);
        self.input_count += 1;
        if self.buffer.len() >= self.batch_size {
            self.flush_batch();
        }
    }

    /// Force-flush the current partial batch.
    fn flush_batch(&mut self) {
        if self.buffer.is_empty() {
            return;
        }
        let batch_data = encode_batch(&self.buffer);
        let key = format!("batch_{:06}.bin", self.batch_count);
        self.batch_count += 1;
        self.buffer.clear();
        if let Some(ref tx) = self.tx {
            let _ = tx.send(BatchMsg::Upload { key, data: batch_data });
        }
    }

    /// Flush remaining data and wait for all uploads to complete.
    /// Returns (batches_uploaded, total_inputs).
    pub fn finish(mut self) -> (u64, u64) {
        self.flush_batch();
        if let Some(tx) = self.tx.take() {
            let _ = tx.send(BatchMsg::Shutdown);
        }
        let batches = self.handle
            .take()
            .and_then(|h| h.join().ok())
            .unwrap_or(0);
        (batches, self.input_count)
    }

    pub fn input_count(&self) -> u64 { self.input_count }
}

impl Drop for BatchUploader {
    fn drop(&mut self) {
        self.flush_batch();
        if let Some(tx) = self.tx.take() {
            let _ = tx.send(BatchMsg::Shutdown);
        }
        if let Some(h) = self.handle.take() {
            let _ = h.join();
        }
    }
}

/// Stream batch objects from S3, decode each, and call `process` for every input.
/// Returns total inputs processed.
pub async fn stream_batches<F>(
    client: &aws_sdk_s3::Client,
    bucket: &str,
    prefix: &str,
    process: F,
) -> Result<u64, Box<dyn std::error::Error>>
where
    F: FnMut(Vec<u8>),
{
    stream_batches_sharded(client, bucket, prefix, 0, 1, process).await
}

/// Like [`stream_batches`], but replays only shard `shard` of `shards` — a CONTIGUOUS
/// slice of the sorted batch list (batch order == collection/stream order). This lets N
/// worker processes each replay ~1/N of a rep's corpus (downloading only their own
/// batches, no redundant GETs), and — because each shard is a contiguous prefix-range —
/// their per-shard coverage profraws cumulative-merge back into the true over-time curve
/// (same pattern as the diversity chunking). `shard` in `0..shards`; `shards >= 1`.
pub async fn stream_batches_sharded<F>(
    client: &aws_sdk_s3::Client,
    bucket: &str,
    prefix: &str,
    shard: usize,
    shards: usize,
    mut process: F,
) -> Result<u64, Box<dyn std::error::Error>>
where
    F: FnMut(Vec<u8>),
{
    let shards = shards.max(1);
    let mut processed = 0u64;
    let mut paginator = client
        .list_objects_v2()
        .bucket(bucket)
        .prefix(prefix)
        .into_paginator()
        .send();

    let mut keys: Vec<String> = Vec::new();
    while let Some(page) = paginator.next().await {
        let page = page?;
        for obj in page.contents() {
            if let Some(key) = obj.key() {
                if key.ends_with(".bin") {
                    keys.push(key.to_string());
                }
            }
        }
    }
    keys.sort();

    // Contiguous slice for this shard: keys[start..end]. div_ceil keeps every batch
    // assigned to exactly one shard (the last shard may get fewer).
    let per = keys.len().div_ceil(shards);
    let start = (shard * per).min(keys.len());
    let end = ((shard + 1) * per).min(keys.len());

    for key in &keys[start..end] {
        let resp = client.get_object().bucket(bucket).key(key).send().await?;
        let bytes = resp.body.collect().await?.into_bytes().to_vec();
        let inputs = decode_batch(&bytes);
        for input in inputs {
            process(input);
            processed += 1;
        }
    }

    Ok(processed)
}

/// Stream objects from S3 under a prefix, calling `process` for each one.
/// Objects are fetched one at a time in sorted key order.
pub async fn stream_objects<F>(
    client: &aws_sdk_s3::Client,
    bucket: &str,
    prefix: &str,
    mut process: F,
) -> Result<u64, Box<dyn std::error::Error>>
where
    F: FnMut(&str, Vec<u8>),
{
    let mut processed = 0u64;
    let mut paginator = client
        .list_objects_v2()
        .bucket(bucket)
        .prefix(prefix)
        .into_paginator()
        .send();

    let mut keys: Vec<String> = Vec::new();
    while let Some(page) = paginator.next().await {
        let page = page?;
        for obj in page.contents() {
            if let Some(key) = obj.key() {
                keys.push(key.to_string());
            }
        }
    }
    keys.sort();

    for key in &keys {
        let relative = key.strip_prefix(prefix).unwrap_or(key).trim_start_matches('/');
        if relative.is_empty() {
            continue;
        }
        let resp = client.get_object().bucket(bucket).key(key).send().await?;
        let bytes = resp.body.collect().await?.into_bytes().to_vec();
        process(relative, bytes);
        processed += 1;
    }

    Ok(processed)
}
