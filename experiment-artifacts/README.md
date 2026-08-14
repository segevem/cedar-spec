# experiment-artifacts

Loose experiment results and charts backed up from the Cloud Desktop home
directory (`/local/home/segevem/`) on 2026-08-14, as part of the pre-AWS-pause
backup. These were not previously under version control.

- `home-charts/` — standalone result charts (coverage/throughput/fuzz-vs-specimen
  comparisons) and `diagnose_output.txt` from the home top level.
- `l4_graphs*`, `illtyped_*_graphs`, `symcc_*_graphs`, `validation_*_graphs`,
  `nonboost_*_graphs`, `l4_welltyped_reject/` — per-run summary graphs + the
  bootstrap-CI / over-time JSON behind them.
- `exp-final-specimen/`, `exp-fresh-specimen/`, `exp2smoke/` — small
  throughput result sets.

Scanned clean of credentials, account IDs, S3 bucket names, and internal
hostnames before commit. The ~10.7 GB of raw experiment output
(`exp2out/`, `exp3/`, `exp-5min-specimen/`, `exp-10min-specimen/`) was
intentionally NOT included — regenerable and too large for git.
