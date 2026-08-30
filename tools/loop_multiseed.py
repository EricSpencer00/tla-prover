"""Pool framing-L seeds against framing-A control seeds.

A single seed can land either side of the pre-registered threshold -- measured:
seed 1 was +6 (p=0.031, WIN) and seed 2 was +4 (p=0.125, NULL) against the same
control. That is exactly the instability W4DG_GATE2_SESSION_2026-07-29.md warned
about for single-run spec-level pass@k, so the claim has to rest on seeds, not on
one run.

Reports, per arm: mean/min/max solved, which specs are solved in EVERY seed
(stable) vs SOME seed (fragile), and the paired gain/loss ledger pooled over all
(seed_L, seed_A) pairs with a sign test on the distinct specs that ever move.

Usage: python3 tools/loop_multiseed.py --loop <dirs...> --open <dirs...>
"""
import argparse
import collections
import json
import math
from pathlib import Path


def pass_set(run_dir):
    seen = {}
    for line in (Path(run_dir) / "rows.jsonl").read_text().splitlines():
        if not line.strip():
            continue
        r = json.loads(line)
        if str(r.get("sample")) == "corruption":
            continue
        key = (r.get("spec"), str(r.get("sample")))
        cur = seen.get(key)
        if cur is None or (cur.get("verdict") == "api_error"
                           and r.get("verdict") != "api_error"):
            seen[key] = r
    by = collections.defaultdict(list)
    for r in seen.values():
        by[r["spec"]].append(r)
    return ({s for s, rs in by.items() if any(x.get("verdict") == "pass" for x in rs)},
            set(by), len(seen))


def sign_test(b, c):
    n = b + c
    if n == 0:
        return 1.0
    k = min(b, c)
    return min(1.0, 2 * sum(math.comb(n, i) for i in range(k + 1)) / (2 ** n))


def summarize(label, dirs):
    sets, specs, calls = [], set(), []
    for d in dirs:
        p, allspecs, n = pass_set(d)
        sets.append(p)
        specs |= allspecs
        calls.append(n)
    sizes = [len(s) for s in sets]
    every = set.intersection(*sets) if sets else set()
    some = set.union(*sets) if sets else set()
    print(f"{label}: {len(dirs)} seed(s)  solved " +
          "/".join(str(x) for x in sizes) +
          f"  mean {sum(sizes)/len(sizes):.1f}/{len(specs)}"
          f"  calls " + "/".join(str(c) for c in calls))
    print(f"    solved in EVERY seed: {len(every)}   in SOME seed: {len(some)}"
          f"   seed-fragile: {sorted(some - every, key=lambda s: int(s))}")
    return sets, every, some, specs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--loop", nargs="+", required=True)
    ap.add_argument("--open", nargs="+", required=True)
    a = ap.parse_args()

    Ls, L_every, L_some, specs = summarize("framing L ", a.loop)
    As, A_every, A_some, _ = summarize("open-loop ", a.open)

    print("\npaired over every (L seed, A seed) combination:")
    gained, lost, deltas = collections.Counter(), collections.Counter(), []
    for i, L in enumerate(Ls):
        for j, A in enumerate(As):
            g, l = sorted(L - A, key=lambda s: int(s)), sorted(A - L, key=lambda s: int(s))
            deltas.append(len(L) - len(A))
            gained.update(g)
            lost.update(l)
            print(f"  L{i+1} vs A{j+1}: {len(L)} vs {len(A)} = {len(L)-len(A):+d}"
                  f"   gained {len(g)} {g}   lost {len(l)} {l}"
                  f"   p={sign_test(len(g), len(l)):.4f}")
    print(f"\ndelta across all pairings: min {min(deltas):+d}  max {max(deltas):+d}  "
          f"mean {sum(deltas)/len(deltas):+.1f}")
    b, c = len(gained), len(lost)
    print(f"distinct specs EVER gained by L: {b} {sorted(gained, key=lambda s: int(s))}")
    print(f"distinct specs EVER lost by L  : {c} {sorted(lost, key=lambda s: int(s))}")
    print(f"sign test on distinct movers   : p = {sign_test(b, c):.4f}")
    print("\nNOTE: the 'ever gained' set is a max-statistic over seeds and is "
          "optimistic;\nthe per-pairing rows above are the honest per-run picture.")

    # Per-spec solve RATE across seeds is the most informative view: it separates
    # "L reliably solves this and open-loop never does" from "one lucky draw".
    print(f"\nper-spec solve rate (L over {len(Ls)} seeds vs open-loop over "
          f"{len(As)} seeds), specs where they differ:")
    rows = []
    for s in sorted(specs, key=lambda x: int(x) if x.isdigit() else 0):
        lr = sum(1 for S in Ls if s in S)
        ar = sum(1 for S in As if s in S)
        if lr / len(Ls) != ar / len(As):
            rows.append((s, lr, ar))
    for s, lr, ar in sorted(rows, key=lambda r: -(r[1] / len(Ls) - r[2] / len(As))):
        bar = "#" * lr + "." * (len(Ls) - lr)
        bar2 = "#" * ar + "." * (len(As) - ar)
        tag = ("L only, every seed" if lr == len(Ls) and ar == 0 else
               "L only, some seeds" if ar == 0 else
               "open-loop only" if lr == 0 else "mixed")
        print(f"  spec {s:>4}  L {bar} {lr}/{len(Ls)}   A {bar2} {ar}/{len(As)}   {tag}")
    always = [s for s, lr, ar in rows if lr == len(Ls) and ar == 0]
    print(f"\nsolved by the loop in EVERY seed and by open-loop in NONE: "
          f"{len(always)} {always}")


if __name__ == "__main__":
    main()
