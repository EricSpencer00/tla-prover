# Session coordination (2026-07-14 ~21:10)
Two Claude sessions ran gen-eval framing B concurrently 19:18-19:21 (dual writers)
-> rows.jsonl has DUPLICATE (spec,sample) pairs for specs 2, 5, 13, 14.
- Run ownership now: the 21:00 relaunch (patched runner.py 1f0536c) is the SOLE writer.
- The tunnel/serve (job 165086, sophia-gpu-06, ctx 32768) + endpoint guard are owned by the
  session that submitted 165086. Do not cycle the serve without checking qstat first.
- At scoring: dedup keep-FIRST per (spec,sample); flag specs 2/5/13/14 in Amendment 16.
- Do NOT launch another gen-eval against run-id gate2-v2-120b-B while pid check
  (pgrep -f 'harness gen-eval') shows a live process.
