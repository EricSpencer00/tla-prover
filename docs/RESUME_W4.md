# How to resume the W4 corpus build (written 2026-07-19 at the usage-pause)

State at pause: 1,848 effective cross-family Opus-teacher survivors (33 waves,
shards 0-73 committed; wave 34 = shards 74-75 was dispatched but stopped before
producing output — its cells 1850-1900 are UNUSED and should be re-assigned).
Corpus total ~2.72k verified rows (~54% of the proposed 5k train floor).
Checkpoint commit: 27fff3a. Session-agnostic recipe — any Claude session can
continue with only this file + the repo.

## Per-wave loop (repeat until the floor or a new decision)

1. Generate the next 50 cells (N = first unused lattice position, currently 1850):
   python3 -c "
   from harness.w4_scenarios import lattice, DOMAINS, MECHANISMS, PROPERTIES, TWISTS, cell_key
   N=1850; S=74   # S = first unused shard number, currently 74
   cells = lattice(20260718, N+50)[N:N+50]
   for s in range(2):
       sl = cells[s*25:(s+1)*25]
       with open(f'/tmp/shard{S+s}.txt','w') as f:
           for c in sl:
               f.write(f'  {cell_key(c)} | {DOMAINS[c[0]]} | {MECHANISMS[c[1]]} | {PROPERTIES[c[2]]} | {TWISTS[c[3]]}\n')"

2. Dispatch 2 Opus subagents (Agent tool, model=opus, run_in_background), one per
   shard file, with the CURRENT canonical brief. The brief has evolved through 33
   waves of incident response — reuse the latest version verbatim from this
   session's shard-74/75 dispatch (git log context) or reconstruct from these
   REQUIRED clauses, all load-bearing:
   - output dir results/runs/w4-opus-shard<S>; touch nothing else; scratch in /tmp
   - complexity tier HARD floors: 40-90 non-comment LOC, 4-6 vars, >=4 actions,
     <100k states; check floors BEFORE appending
   - anti-self-copy: every cell from scratch; shingle audit quarantines
   - ledger: append-only, one survivor row per cell, FULL cell key in cell/seed_key,
     never edit/strip rows, corrections as new rows flagged keep-last
   - per cell: NL scenario ending "SAFETY PROPERTY: <sentence>" AND (since
     2026-07-23, Eric's liveness call) "LIVENESS PROPERTY: <sentence>"; NL
     updated BEFORE final verify when actions change; module W4O<key-no-dashes>;
     verify via `python3 -m harness.w4_verify_cell --nl .. --spec .. --cfg ..
     --invariant .. --workdir /tmp/... --require-liveness`; max 4 attempts;
     survivors merged with
   - LIVENESS (mandatory on every cell from shard 129 on): the spec must define
     a real eventuality (<> or ~>) implementing the NL's LIVENESS PROPERTY,
     Spec must include the WF_/SF_ fairness that makes it true, and the .cfg
     must check it with a PROPERTY line. The harness FIX-5 gate re-runs TLC
     with fairness stripped and REJECTS "liveness_stutter_trivial" unless the
     property FAILS there -- so an Init-true or stutter-insensitive eventuality
     cannot pass. Do not game with <>TRUE-shaped properties; write progress
     properties the mechanism actually guarantees (e.g. "every admitted request
     is eventually serviced", "the token eventually returns to the ring").
     {"cell","seed_key":"w4opus::<full-key>","nl","teacher":"claude-opus","tier":"complex"}
   - INTEGRITY: no mutation.py access of ANY kind (a violator shard's evidence was
     flagged untrusted); on typeok_only rejections restructure naturally; no
     engineered mutation-catch constructs; no_kill/no_site acceptable
   - DIVERSITY: avoid `Cardinality(S)<=1`, `applied+Len(queue)=admitted`, ghost
     `badActions=0`, bare `count<=1`, pairwise slot-uniqueness,
     counter-vs-cardinality where honest alternatives exist
   - RETURN: survivors/attempted, reject histogram, median LOC+states, 3 hardest
     cells, honesty note

3. AFTER BOTH shards report, run the audit (paste as-is, bump range end):
   python3 - <<'PYEOF'
   import json, itertools
   from pathlib import Path
   from harness.corpora import shingle_set, normalize_tla, SHINGLE_K, NEAR_DUP_THRESHOLD
   d=json.load(open("results/analysis/w4_exclusions.json"))
   excl=set(d["excluded_seed_keys"]); keeplast=set(d.get("dedup_overrides",{}))
   rows={}
   for s in range(76):   # <-- last shard + 1
       p=Path(f"results/runs/w4-opus-shard{s}/w2_survivors.jsonl")
       if not p.exists(): continue
       for l in p.read_text().splitlines():
           if l.strip():
               r=json.loads(l); k=r.get("seed_key")
               if k in excl: continue
               if k in rows and k not in keeplast: continue
               rows[k]=r
   rows=list(rows.values())
   sh=[shingle_set(normalize_tla(r["spec_text"]),SHINGLE_K) for r in rows]
   jac=lambda a,b: len(a&b)/max(1,len(a|b))
   bad=[(round(jac(sh[i],sh[j]),3),rows[i]["seed_key"],rows[j]["seed_key"])
        for i,j in itertools.combinations(range(len(rows)),2)
        if jac(sh[i],sh[j])>=NEAR_DUP_THRESHOLD]
   print(f"effective corpus {len(rows)}; near-dups: {bad if bad else 'NONE'}")
   PYEOF

4. Handle incidents exactly as the ledgered precedents (results/analysis/
   w4_exclusions.json holds all state): near-dup pair -> add loser to
   excluded_seed_keys; double-append/keep-last disclosure -> add to
   dedup_overrides; agent claims done but ledger short -> SendMessage the agent to
   finish missing cells; mutation-gate engineering disclosure -> add seed_keys to
   mutation_evidence_untrusted + note. Every shard report gets read for honesty
   flags before commit.

5. Commit: `git add results/runs/w4-opus-shard<S> results/runs/w4-opus-shard<S+1>
   results/analysis/w4_exclusions.json && git commit` with the wave count +
   effective total in the message. Update memory round3-status counts.

## When the corpus is deemed big enough (Eric's call; proposed floor 5k rows total)
Render + gate per round3-status "AFTER HARVEST" notes: corpus_prep sft over all
w4-opus-shard* dirs (honor w4_exclusions.json exclusions + keep-last overrides
and the shard-50 short-key mapping in commit 81bfb65), then the ONE pre-registered
120b train+eval per Amendment 17's re-entry condition. Also outstanding: Eric's
explicit calls on (a) full-rate vs half-rate waves, (b) the gated train run,
(c) publishing/HF upload.

## Cost calibration (measured)
~500k Opus subagent tokens per 50-spec wave; ~25-35 min/wave wall; 100% survival
across all 33 waves; audit catches ~1 incident per 2-3 waves (all recoverable).
