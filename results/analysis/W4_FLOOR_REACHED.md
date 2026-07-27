# W4 floor reached

`tools/w4_audit.py` reported `STOP=YES` after wave (cloud) shards 199-200. Verbatim output:

```
shards 0-200; effective corpus 5010 (liveness arm 567, safety-only 4443)
  total    5010/5000 MET
  liveness 567/500 MET (11.3% of corpus)
  family   top=mutex_locks 1788 (35.7%) OVER 30% (advisory)
  families: mutex_locks=1788  other=895  consensus=786  queues_buffers=458  commit_protocols=444  counters_registers=394  network_channels=155  caches_memory=47  replication_storage=43
  tiers:    diamond=607(94L)  gold=3612(466L)  silver=693(7L)  bronze=98(0L)
  mutation: no_kill=3169  no_site=1200  safety_catch=641  (real-catch 12.8%)
  cfg: thin(<=3 lines) 1310 (26.1%)  SPECIFICATION 2295  CONSTANT 3679  PROPERTY 567
  near-dups (shards>=199): NONE
STOP=YES
```

Both the total (5000) and liveness-arm (500) floors are met. The family-share line
(`mutex_locks` at 35.7%, over the 30% advisory line) does not gate stopping — it is
advisory only, per the stop rule in `docs/W4_CELL_RULES.md`.

The cloud wave routine (`docs/RESUME_W4.md`) should not run further waves against
this corpus once this file is present.
