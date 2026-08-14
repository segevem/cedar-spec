//! Wall-clock timeout wrapper around the Lean generation FFI.
//!
//! The Specimen generators can, on rare pathological seeds, spin indefinitely
//! (e.g. `backtrackFuel` exploding in the `CapMerge`/`TypeOfCheck` rule). A
//! synchronous Lean FFI call cannot be interrupted in-process, so we run each
//! generation call on a dedicated worker thread and bound it with a timeout.
//!
//! On timeout the offending seed is LOGGED and the (still-spinning) worker is
//! abandoned; a fresh worker is spawned so generation continues from the next
//! seed. This turns a whole-run hang into a single logged+skipped seed. We NEVER
//! abort the rep on timeouts — skipping and continuing is the whole point. The
//! abandoned worker finishes its fuel-bounded Lean computation and exits on its
//! own (its reply send then fails harmlessly), so leaked workers self-clear.
//!
//! `CedarLeanFfi` initializes the *calling thread* for the Lean runtime (module
//! init is a global `Once`), so creating one inside each worker thread — and
//! leaving leaked workers Lean-initialized — is safe.

use std::cell::RefCell;
use std::sync::mpsc::{self, Receiver, RecvTimeoutError, Sender};
use std::thread;
use std::time::Duration;

use cedar_lean_ffi::CedarLeanFfi;

/// Which generation FFI to invoke on the worker.
#[derive(Clone, Copy)]
pub enum GenKind {
    /// `generate_typeof_proto` (fixed schema, terms only).
    Typeof,
    /// `generate_schema_typeof_proto` (random schema + batch of terms).
    SchemaTypeof,
}

struct Job {
    kind: GenKind,
    params: serde_json::Value,
}
type Reply = Result<Vec<u8>, String>;

struct Inner {
    job_tx: Sender<Job>,
    reply_rx: Receiver<Reply>,
    /// Number of workers abandoned to a timeout so far (leaked, spinning cores).
    abandoned: usize,
}

/// Timeout-bounded handle to the Lean generation FFI. Shares the same method
/// names as [`CedarLeanFfi`] but returns `Option` (None = timed out or errored).
pub struct TimeoutFfi {
    inner: RefCell<Inner>,
    timeout: Duration,
}

impl TimeoutFfi {
    pub fn new() -> Self {
        let timeout_secs: f64 = std::env::var("GENERATE_TIMEOUT_SECS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(10.0);
        let (job_tx, reply_rx) = Self::spawn_worker();
        TimeoutFfi {
            inner: RefCell::new(Inner { job_tx, reply_rx, abandoned: 0 }),
            timeout: Duration::from_secs_f64(timeout_secs),
        }
    }

    /// Spawn a worker thread that owns a fresh `CedarLeanFfi` (which initializes
    /// that thread for the Lean runtime) and services generation jobs until its
    /// job channel is dropped.
    fn spawn_worker() -> (Sender<Job>, Receiver<Reply>) {
        let (job_tx, job_rx) = mpsc::channel::<Job>();
        let (reply_tx, reply_rx) = mpsc::channel::<Reply>();
        thread::spawn(move || {
            let ffi = CedarLeanFfi::new();
            while let Ok(job) = job_rx.recv() {
                let res = match job.kind {
                    GenKind::Typeof => ffi.generate_typeof_proto(&job.params),
                    GenKind::SchemaTypeof => ffi.generate_schema_typeof_proto(&job.params),
                };
                if reply_tx.send(res.map_err(|e| e.to_string())).is_err() {
                    break; // handle was dropped/respawned; stop cleanly
                }
            }
            // `ffi` drops here -> lean_finalize_thread for a cleanly-exited worker.
        });
        (job_tx, reply_rx)
    }

    /// Replace the current worker with a fresh one, abandoning the old (stuck)
    /// thread. We NEVER abort the rep: a slow/hanging seed is logged and skipped
    /// and generation continues — that is the whole point of the timeout. The
    /// abandoned worker finishes its (fuel-bounded) Lean computation and exits on
    /// its own; its `reply_tx` send then fails harmlessly and the thread returns.
    fn respawn(&self, inner: &mut Inner) {
        let (job_tx, reply_rx) = Self::spawn_worker();
        inner.job_tx = job_tx;
        inner.reply_rx = reply_rx;
        inner.abandoned += 1;
    }

    fn call(&self, kind: GenKind, params: &serde_json::Value) -> Option<Vec<u8>> {
        let mut inner = self.inner.borrow_mut();
        if inner.job_tx.send(Job { kind, params: params.clone() }).is_err() {
            self.respawn(&mut inner);
            inner.job_tx.send(Job { kind, params: params.clone() }).ok()?;
        }
        match inner.reply_rx.recv_timeout(self.timeout) {
            Ok(Ok(bytes)) => Some(bytes),
            Ok(Err(_ffi_err)) => None,
            Err(RecvTimeoutError::Timeout) => {
                // Log the offending seed/params so it can be reproduced. This
                // lands in the per-rep stderr log (uploaded to S3 results/).
                eprintln!(
                    "SLOW_SEED timeout={:.1}s abandoned={} params={}",
                    self.timeout.as_secs_f64(),
                    inner.abandoned + 1,
                    params
                );
                self.respawn(&mut inner);
                None
            }
            Err(RecvTimeoutError::Disconnected) => {
                self.respawn(&mut inner);
                None
            }
        }
    }

    /// Timeout-bounded [`CedarLeanFfi::generate_typeof_proto`].
    pub fn generate_typeof_proto(&self, params: &serde_json::Value) -> Option<Vec<u8>> {
        self.call(GenKind::Typeof, params)
    }

    /// Timeout-bounded [`CedarLeanFfi::generate_schema_typeof_proto`].
    pub fn generate_schema_typeof_proto(&self, params: &serde_json::Value) -> Option<Vec<u8>> {
        self.call(GenKind::SchemaTypeof, params)
    }
}

impl Default for TimeoutFfi {
    fn default() -> Self {
        Self::new()
    }
}
