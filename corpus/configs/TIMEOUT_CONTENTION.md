# Parallelism-induced false timeouts

Running the full oracle sweep at `--jobs 8` produces some `tlc=timeout` results that
are not genuine large-state-space specs — they're victims of CPU/memory contention
among 8 concurrent JVM processes on this machine. Discovered while re-verifying
spec 141 (closed via the sibling-wrapper fix in `SIBLING_WRAPPERS.md`): it showed
`tlc=timeout` in `results/runs/gate0-sweep-v4` (`--jobs 8`) but passes in under a
second alone (`results/runs/spec141-isolated`).

Re-ran every spec that showed `tlc=timeout` in `gate0-sweep-v4` at `--jobs 2` instead
of 8 (`results/runs/timeout-recheck-isolated`, `.../timeout-recheck-isolated2`).
Confirmed false timeouts (genuinely close at lower parallelism), 3 of 22:

- **31** — passes cleanly at `--jobs 2`.
- **135** (MCReachable) — passes cleanly at `--jobs 2`.
- **141** (Reachable, wired to 135 via the sibling-wrapper fix) — passes cleanly alone.

The other 19 (1, 12, 14, 16, 17, 28, 30, 35, 36, 40, 47, 48, 49, 57, 73, 79, 89, 107,
146) still time out even at `--jobs 2`, consistent with the genuinely-large-state-space
findings already documented for specs like 30 (Agreement violation open,
`PATCHES.md`), 48/49/146 (`CANONICAL_MODEL_FIXES.md`, `MC_WRAPPERS.md`, sustained
multi-million-state/minute growth confirmed via dedicated longer runs) — those
findings stand.

**Implication for future sweeps:** a full-corpus run at high `--jobs` undercounts true
closures. `GATE0_STATUS.md`'s numbers below account for this correction (31, 135, 141
counted as closed), but a systematic fix (lower parallelism, or a two-pass sweep where
timeouts get one retry at low parallelism before being counted) would be more honest
than a one-off manual correction — not implemented here, noted as follow-on work.
