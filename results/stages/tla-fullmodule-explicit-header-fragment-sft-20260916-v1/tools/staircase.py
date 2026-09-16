"""Per-spec staircase over every valid ledger: deepest rung each holdout spec
has EVER reached, and by which run.

The ralph staircase loop (docs/RALPH_STAIRCASE.md) ranks its work by this
table: the shallowest rung with gaps is the one to attack. Rungs:

  0 none        no row ever extracted a module for the spec
  1 module      module extracted, SANY never passed
  2 sany        SANY passed; terminal rung for LIBRARIES / PROOF_MODULES pops
  3 tlc_vacuous TLC accepted but Rule-5 vacuity tripped
  4 pass        verdict == "pass" (TLC accepted, vacuity clean)

Mutation sensitivity (the Diamond rung) is only measured by framing-B
corruption runs and framing-B scores repairs, not generation, so it is
reported separately, not as rung 5.

Excluded run dirs: QUARANTINE-*, smoke*, drytest*, lewm* (different task),
plus anything without rows.jsonl. Dedup within a run follows gate_check
semantics (keep first scored row per (spec, sample)).
"""
import json
import sys
from collections import defaultdict
from pathlib import Path

HOLDOUT = ["2", "5", "13", "14", "15", "30", "32", "37", "41", "55", "86",
           "95", "105", "106", "121", "128", "131", "132", "133", "135",
           "141", "142", "143", "148", "158", "168", "174", "181", "183",
           "191"]
# populations from corpus/holdout_30.json: SANY is terminal for these
SANY_TERMINAL = {"41", "86", "105", "183",      # LIBRARIES
                 "128", "158"}                   # PROOF_MODULES (TLAPS-graded)

RUNG_NAMES = {0: "none", 1: "module", 2: "sany", 3: "tlc_vacuous", 4: "pass"}


def rung_of(row):
    v = str(row.get("verdict", ""))
    if v == "pass":
        return 4
    if row.get("sany") == "pass":
        if row.get("tlc") in ("pass", "ok") or "vacuous" in v:
            return 3
        return 2
    if v in ("api_error", "no_module_extracted") or v.startswith("skipped"):
        return 0
    return 1


def scan(runs_dir):
    best = {s: (0, None) for s in HOLDOUT}   # spec -> (rung, run_id)
    attempts = defaultdict(int)
    for d in sorted(Path(runs_dir).iterdir()):
        name = d.name
        if (name.startswith("QUARANTINE") or name.startswith("smoke")
                or name.startswith("drytest") or name.startswith("lewm")
                or not (d / "rows.jsonl").is_file()):
            continue
        for line in (d / "rows.jsonl").read_text().splitlines():
            if not line:
                continue
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            s = str(r.get("spec"))
            if s not in best or str(r.get("sample")) == "corruption":
                continue
            attempts[s] += 1
            rung = rung_of(r)
            if s in SANY_TERMINAL and rung >= 2:
                rung = 4                      # SANY is this spec's summit
            if rung > best[s][0]:
                best[s] = (rung, name)
    return best, attempts


def main():
    runs_dir = sys.argv[1] if len(sys.argv) > 1 else "results/runs"
    best, attempts = scan(runs_dir)
    by_rung = defaultdict(list)
    for s in HOLDOUT:
        by_rung[best[s][0]].append(s)
    print(f"{'spec':>5} {'rung':<12} {'rows':>6}  first run to reach it")
    for s in sorted(HOLDOUT, key=lambda x: (best[x][0], int(x))):
        rung, run = best[s]
        star = " *" if s in SANY_TERMINAL else ""
        print(f"{s:>5} {RUNG_NAMES[rung]:<12} {attempts[s]:>6}  {run or '-'}{star}")
    print("\n(* = SANY-terminal population; rung 'pass' there means SANY pass)")
    solved = len(by_rung[4])
    print(f"\nsummit reached ever: {solved}/30")
    for rung in (0, 1, 2, 3):
        if by_rung[rung]:
            print(f"stuck at {RUNG_NAMES[rung]:<12}: "
                  f"{sorted(by_rung[rung], key=int)}")


if __name__ == "__main__":
    main()
