"""Emit every number the addendum reports, from the ledgers, into one JSON.

Nothing in the paper is typed by hand: the tables and figures are generated from
this file, so a stale number cannot survive a re-run. Ledgers are re-scored here
with keep-first dedup rather than read from summary.json -- the base arm's
committed summary.json says 1/30 where its ledger says 12/30.
"""
import collections
import json
import math
import os
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO))
from harness.gen_eval import required_signature          # noqa: E402
from harness.loop_eval import missing_signature, wrapper_text_for  # noqa: E402
from harness.runner import build_module_index            # noqa: E402

LOOP = ["loop-base-120b", "loop-base-120b-seed2", "loop-base-120b-seed3"]
OPEN = ["open-base-120b-samesession", "open-base-120b-seed3", "e2c-baseline-120b-a"]
CORPUS = Path("/Users/eric/GitHub/tla_benchmark/data")


def rows(run):
    seen = {}
    p = REPO / "results" / "runs" / run / "rows.jsonl"
    for line in p.read_text().splitlines():
        if not line.strip():
            continue
        r = json.loads(line)
        if str(r.get("sample")) == "corruption":
            continue
        seen.setdefault((r.get("spec"), str(r.get("sample"))), r)
    return list(seen.values())


def solved(rs):
    by = collections.defaultdict(list)
    for r in rs:
        by[r["spec"]].append(r)
    return {s for s, v in by.items() if any(x.get("verdict") == "pass" for x in v)}


def sign_test(b, c):
    n = b + c
    if n == 0:
        return 1.0
    k = min(b, c)
    return min(1.0, 2 * sum(math.comb(n, i) for i in range(k + 1)) / (2 ** n))


def main():
    out = {}

    # ---- arm-level results -------------------------------------------------
    arms = {}
    for name in LOOP + OPEN:
        rs = rows(name)
        arms[name] = {
            "solved": sorted(solved(rs), key=lambda s: int(s)),
            "n_solved": len(solved(rs)),
            "model_calls": len(rs),
            "sany_pass_rows": sum(1 for r in rs if r.get("sany") == "pass"),
            "rows": len(rs),
        }
    out["arms"] = arms
    out["loop_runs"], out["open_runs"] = LOOP, OPEN
    out["loop_solved"] = [arms[r]["n_solved"] for r in LOOP]
    out["open_solved"] = [arms[r]["n_solved"] for r in OPEN]
    out["loop_calls"] = [arms[r]["model_calls"] for r in LOOP]
    out["open_calls"] = [arms[r]["model_calls"] for r in OPEN]

    pair = []
    for i, L in enumerate(LOOP):
        for j, A in enumerate(OPEN):
            g = sorted(set(arms[L]["solved"]) - set(arms[A]["solved"]), key=lambda s: int(s))
            l = sorted(set(arms[A]["solved"]) - set(arms[L]["solved"]), key=lambda s: int(s))
            pair.append({"loop": L, "open": A,
                         "delta": arms[L]["n_solved"] - arms[A]["n_solved"],
                         "gained": g, "lost": l, "p": sign_test(len(g), len(l))})
    out["pairings"] = pair

    # per-spec solve rate across seeds
    specs = sorted({s for a in arms.values() for s in a["solved"]}
                   | set(json.loads((REPO / "results" / "runs" / LOOP[0] /
                                     "config.json").read_text())["holdout_specs"]),
                   key=lambda s: int(s))
    out["per_spec"] = [{"spec": s,
                        "loop": sum(1 for r in LOOP if s in arms[r]["solved"]),
                        "open": sum(1 for r in OPEN if s in arms[r]["solved"])}
                       for s in specs]

    # calls-to-solve and which rung rescued each spec (seed 1, the only arm with
    # chain/round provenance reported in the text)
    cts = []
    for r in rows(LOOP[0]):
        if r.get("verdict") == "pass":
            cts.append({"spec": r["spec"], "calls": r.get("calls_used"),
                        "round": r.get("round"), "rung": r.get("rung_in")})
    out["calls_to_solve"] = sorted(cts, key=lambda d: d["calls"] or 0)

    # ---- spec-level SANY coverage -----------------------------------------
    cov = collections.defaultdict(lambda: [0, 0])
    for name in LOOP + OPEN:
        for r in rows(name):
            if not r.get("sany"):
                continue
            cov[r["spec"]][1] += 1
            if r["sany"] == "pass":
                cov[r["spec"]][0] += 1
    out["sany_coverage"] = [{"spec": s, "pass": v[0], "draws": v[1]}
                            for s, v in sorted(cov.items(), key=lambda kv: int(kv[0]))]
    out["specs_with_zero_parse"] = [s for s, v in cov.items() if v[0] == 0]

    # ---- SANY failure taxonomy --------------------------------------------
    CLASSES = [("parse", re.compile(r"Could not parse module")),
               ("unknown_operator", re.compile(r"Unknown operator")),
               ("duplicate_definition", re.compile(r"Multiple declarations")),
               ("arity", re.compile(r"requires \d+ argument")),
               ("level", re.compile(r"[Ll]evel error")),
               ("substitution", re.compile(r"Substitution missing"))]
    tax = collections.Counter()
    unk = collections.Counter()
    n_fail = 0
    MODHDR = re.compile(r"^\s*-{4,}\s*MODULE\s+(\w+)", re.M)
    for name in LOOP + OPEN:
        run = REPO / "results" / "runs" / name
        for r in rows(name):
            if r.get("sany") in ("pass", None):
                continue
            lp = r.get("log_path", "")
            if not lp or not os.path.exists(lp):
                continue
            t = open(lp, errors="replace").read()
            n_fail += 1
            hit = next((k for k, rx in CLASSES if rx.search(t)), "other")
            tax[hit] += 1
            cp = r.get("candidate_path")
            if hit != "unknown_operator" or not cp:
                continue
            p = run / cp
            if not p.is_file():
                continue
            mod_text = p.read_text(errors="replace")
            mh = MODHDR.search(mod_text)
            if not mh:
                continue
            modname, lines = mh.group(1), mod_text.splitlines()
            for m in re.finditer(
                    r"line (\d+), col \d+ to line \d+, col \d+ of module (\w+)\s*\n"
                    r"\s*Unknown operator: `(\w+)'", t):
                el, em, nm = int(m.group(1)), m.group(2), m.group(3)
                if em != modname or el > len(lines):
                    continue
                src = lines[el - 1]
                if re.search(rf"\w+!\s*{re.escape(nm)}\b", src):
                    unk["qualified_against_unqualified_instance"] += 1
                    continue
                defre = re.compile(rf"^\s*{re.escape(nm)}\s*(?:\([^)]*\))?\s*(?:==|≜)")
                declre = re.compile(rf"^\s*(?:CONSTANTS?|VARIABLES?)\b.*\b{re.escape(nm)}\b")
                dl = [i + 1 for i, l2 in enumerate(lines)
                      if defre.match(l2) or declre.match(l2)]
                bound = re.search(
                    rf"\\[AE]\s+[\w,\s]*\b{re.escape(nm)}\b\s*\\in|\bLET\b[^\n]*\b{re.escape(nm)}\b"
                    rf"|\bCHOOSE\s+{re.escape(nm)}\b", mod_text)
                if dl and any(d < el for d in dl):
                    unk["defined_earlier_recursive_or_scope"] += 1
                elif dl:
                    unk["forward_reference"] += 1
                elif bound:
                    unk["bound_var_escaped_scope"] += 1
                else:
                    unk["invented_operator"] += 1
    out["sany_failures_total"] = n_fail
    out["sany_taxonomy"] = dict(tax)
    out["unknown_operator_taxonomy"] = dict(unk)

    # ---- offending tokens in the parse-failure population ------------------
    tok = collections.Counter()
    for name in LOOP + OPEN:
        for r in rows(name):
            lp = r.get("log_path", "")
            if r.get("sany") in ("pass", None) or not lp or not os.path.exists(lp):
                continue
            t = open(lp, errors="replace").read()
            if "Could not parse module" not in t:
                continue
            m = re.search(r'Encountered "([^"]{1,40})"', t)
            tok[m.group(1) if m else "(none reported)"] += 1
    out["parse_offending_tokens"] = tok.most_common(14)

    # ---- reachability ceiling: parse and signature completeness ------------
    n2m, m2p = build_module_index(CORPUS)
    cfg_dirs = [REPO / "corpus" / "configs" / "overrides", CORPUS / "cfg",
                REPO / "corpus" / "configs" / "drafts"]
    cfgc, wt = {}, {}

    def cfg_for(s):
        if s not in cfgc:
            cfgc[s] = None
            for d in cfg_dirs:
                if (d / f"{s}.cfg").exists():
                    cfgc[s] = (d / f"{s}.cfg").read_text()
                    break
        return cfgc[s]

    reach = collections.defaultdict(lambda: {"parse": 0, "sig": 0, "tlc": 0, "n": 0})
    for name in LOOP + OPEN:
        run = REPO / "results" / "runs" / name
        for r in rows(name):
            s = r["spec"]
            reach[s]["n"] += 1
            if r.get("sany") != "pass":
                continue
            reach[s]["parse"] += 1
            if r.get("tlc") in ("pass", "pass_expected_violation"):
                reach[s]["tlc"] += 1
            cp, ct = r.get("candidate_path"), cfg_for(s)
            if not cp or not ct:
                continue
            p = run / cp
            if not p.is_file():
                continue
            if s not in wt:
                wt[s] = wrapper_text_for(s, n2m, m2p)
            if not missing_signature(p.read_text(errors="replace"), ct, wt[s]):
                reach[s]["sig"] += 1
    out["reachability"] = {s: dict(v) for s, v in sorted(reach.items(),
                                                        key=lambda kv: int(kv[0]))}
    out["reach_totals"] = {
        "draws": sum(v["n"] for v in reach.values()),
        "parse": sum(v["parse"] for v in reach.values()),
        "signature_complete": sum(v["sig"] for v in reach.values()),
        "tlc": sum(v["tlc"] for v in reach.values()),
        "specs_any_parse": sum(1 for v in reach.values() if v["parse"]),
        "specs_any_sig": sum(1 for v in reach.values() if v["sig"]),
        "specs_any_tlc": sum(1 for v in reach.values() if v["tlc"]),
        "n_specs": len(reach)}

    (Path(__file__).parent / "data.json").write_text(json.dumps(out, indent=1))
    print("wrote", Path(__file__).parent / "data.json")
    print("loop", out["loop_solved"], "open", out["open_solved"])
    print("sany failures", out["sany_failures_total"], dict(tax))
    print("reach", out["reach_totals"])


if __name__ == "__main__":
    main()
