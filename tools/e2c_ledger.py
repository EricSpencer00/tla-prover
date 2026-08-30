"""One ledgered Gate-2 table: the frozen E2.c baseline and every arm that has
challenged it, re-scored from rows.jsonl.

Why this exists: the baseline was frozen in `corpus/e2c_baseline.json`
(Amendment 13) and five challenger arms were measured after it, but each
challenger's numbers live only in its own PLAN amendment. There was no single
artifact a retrain can be held against, and WEEKLY.md still said no Stage-2
baseline existed. This tool builds that artifact from the append-only ledgers,
so the table is recomputed, never transcribed.

Scoring is `harness.gate_check` (keep-first dedup, exclude sample=="corruption",
pass@1 = the temp-0 greedy sample) -- the frozen Amendment-12 definitions. It
never reads summary.json.

Three counts per framing-B cell, because the arms carry different audit debt:
  raw          ledger-true pass count, the column Amendment 16 compared on
  clean_floor  same count restricted to rows the mechanical Rule-9 audit calls
               CLEAN (no checked definition touched) with a verified candidate
               sha256; a worst-case floor that needs no manual reads
  audited      only where a manual Rule-9 triage was completed and signed off

Framing A has no audited column: the baseline's A arms predate candidate
persistence, so no diff audit is possible on them and A stays raw-vs-raw
(disclosed in the freeze artifact).

Usage:
    python3 tools/e2c_ledger.py           # rebuild corpus/e2c_ledger.json + .md
    python3 tools/e2c_ledger.py --check   # verify the committed artifacts
"""
import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))

from harness.gate_check import gate_check, load_rows

# Amendment 13's frozen hash. If corpus/e2c_baseline.json ever stops hashing to
# this, the baseline was edited without a sign-off and every row below is void.
FROZEN_BASELINE_SHA = \
    "f9dc83ec487acfae018475b4557bb7c35b6d844e5310dec33195f0f98a22c545"

JSON_OUT = REPO / "corpus" / "e2c_ledger.json"
MD_OUT = REPO / "results" / "e2c_ledger.md"

# (label, model, framing, run_id, role, amendment, audit_key, note)
ARMS = [
    ("baseline-20b-A", "openai/gpt-oss-20b", "A", "e2c-baseline-20b-a",
     "baseline", 13, None, "untuned base chattla was built on"),
    ("baseline-120b-A", "openai/gpt-oss-120b", "A", "e2c-baseline-120b-a",
     "baseline", 13, None, "frozen baseline arm (best of the two in all four cells)"),
    ("baseline-20b-B", "openai/gpt-oss-20b", "B", "e2c-baseline-r2-20b-b",
     "baseline", 13, "20b", "r2 rerun, candidate-persisted"),
    ("baseline-120b-B", "openai/gpt-oss-120b", "B", "e2c-baseline-r2-120b-b",
     "baseline", 13, "120b", "r2 rerun; 1 Rule-9 reject (spec 15) -> frozen 20/23"),
    ("v2_sft2-A", "chattla-v2-120b", "A", "gate2-v2-120b-A",
     "challenger", 16, None, "260 harmony pairs, full FT"),
    ("v2_sft2-B", "chattla-v2-120b", "B", "gate2-v2-120b-B",
     "challenger", 16, "gate2-v2-120b-B",
     "duplicate writers overwrote 69 candidate files: those rows are unauditable"),
    ("w4dg-A", "chattla-w4dg-120b", "A", "gate2-w4dg-120b-A3",
     "challenger", 22, None, "W4 cross-family corpus, bare rendering"),
    ("w4dg-B", "chattla-w4dg-120b", "B", "gate2-w4dg-120b-B",
     "challenger", 22, "gate2-w4dg-120b-B", "PARTIAL: 4 of 23 specs only"),
    ("w4dgp-A", "chattla-w4dgp-120b", "A", "gate2-w4dgp-120b-A",
     "challenger", 22, None, "prompt-aligned rendering"),
    ("w4dgp-B", "chattla-w4dgp-120b", "B", "gate2-w4dgp-120b-B",
     "challenger", 22, "gate2-w4dgp-120b-B", "prompt-aligned rendering"),
    ("w4dgm-A", "chattla-w4dgm-120b", "A", "gate2-w4dgm-120b-A",
     "challenger", 25, None, "W4DG + 2,787 oracle repair pairs"),
    ("w4dgm-B", "chattla-w4dgm-120b", "B", "gate2-w4dgm-120b-B",
     "challenger", 25, "gate2-w4dgm-120b-B", "W4DG + 2,787 oracle repair pairs"),
]

AUDIT_FILES = {
    "20b": REPO / "results" / "runs" / "r2b_audit_raw.json",
    "120b": REPO / "results" / "runs" / "r2b_audit_raw.json",
}
CHALLENGER_AUDIT = REPO / "results" / "runs" / "challenger_b_audit_raw.json"

# manual Rule-9 triage completed and signed off (Amendment 13 only)
AUDITED = {"baseline-20b-B": 19, "baseline-120b-B": 20}


def audit_path(key):
    return AUDIT_FILES.get(key, CHALLENGER_AUDIT)


def clean_keys(key):
    """(spec, sample) pairs the mechanical audit calls CLEAN with a verified sha."""
    data = json.loads(audit_path(key).read_text())[key]
    mismatched = {(str(x[0]), str(x[1])) for x in data["sha_mismatches"]}
    return {(str(r["spec"]), str(r["sample"])) for r in data["results"]
            if r["verdict"] == "CLEAN"
            and (str(r["spec"]), str(r["sample"])) not in mismatched}, len(mismatched)


def deduped_scored(run_dir):
    """gate_check's keep-first dedup, exposed so the CLEAN floor uses the same rows."""
    rows = load_rows(run_dir)
    seen, order = {}, []
    for r in rows:
        k = (str(r.get("spec")), str(r.get("sample")))
        if k not in seen:
            seen[k] = r
            order.append(k)
        elif seen[k].get("verdict") == "api_error" and r.get("verdict") != "api_error":
            seen[k] = r
    return [seen[k] for k in order if k[1] != "corruption"]


def clean_floor(run_dir, key):
    rows = deduped_scored(run_dir)
    clean, n_mismatch = clean_keys(key)
    specs = sorted({str(r["spec"]) for r in rows})
    ok = [r for r in rows if r.get("verdict") == "pass"
          and (str(r["spec"]), str(r["sample"])) in clean]
    pk = sorted({str(r["spec"]) for r in ok})
    p1 = sorted({str(r["spec"]) for r in ok if str(r["sample"]) == "greedy"})
    return {"pass_at_k": len(pk), "pass_at_1": len(p1), "pass_set": pk,
            "n_specs": len(specs), "unauditable_rows": n_mismatch}


def build():
    arms = []
    for label, model, framing, run_id, role, amendment, key, note in ARMS:
        run_dir = REPO / "results" / "runs" / run_id
        rep = gate_check(run_dir)
        arm = {
            "label": label, "model": model, "framing": framing,
            "run_id": run_id, "role": role, "amendment": amendment,
            "n_specs": rep["specs"],
            "raw": {"pass_at_1": rep["pass_at_1"], "pass_at_k": rep["pass_at_k"],
                    "pass_set": rep["pass_set"]},
            "gate_check_ok": rep["ok"],
            "gate_check_failures": rep["failures"],
            "api_error_rows": rep["api_error_rows"],
            "rows_deduped": rep["rows_deduped"],
            "note": note,
        }
        if key:
            arm["clean_floor"] = clean_floor(run_dir, key)
            arm["audit_status"] = ("manual-triage-complete" if label in AUDITED
                                   else "mechanical-only")
        else:
            arm["audit_status"] = "measurement-time-screens-only"
        if label in AUDITED:
            arm["audited"] = {"pass_at_k": AUDITED[label]}
        arms.append(arm)
    return arms


def frozen_baseline():
    path = REPO / "corpus" / "e2c_baseline.json"
    import hashlib
    sha = hashlib.sha256(path.read_bytes()).hexdigest()
    return json.loads(path.read_text()), sha


def cells(arms):
    """The four Gate-2 cells of the frozen baseline arm, as the bar to beat."""
    a = next(x for x in arms if x["label"] == "baseline-120b-A")
    b = next(x for x in arms if x["label"] == "baseline-120b-B")
    return {
        "A_pass@1": {"value": a["raw"]["pass_at_1"], "n": a["n_specs"]},
        "A_pass@32": {"value": a["raw"]["pass_at_k"], "n": a["n_specs"]},
        "B_pass@1": {"value": b["raw"]["pass_at_1"], "n": b["n_specs"]},
        "B_pass@32": {"value": AUDITED["baseline-120b-B"], "n": b["n_specs"]},
    }


def verdict(arms, label_a, label_b, bar):
    """Gate-2 'beats': >= the bar in all four cells and strictly > in one."""
    a = next(x for x in arms if x["label"] == label_a)
    b = next(x for x in arms if x["label"] == label_b)
    got = {"A_pass@1": a["raw"]["pass_at_1"], "A_pass@32": a["raw"]["pass_at_k"],
           "B_pass@1": b["raw"]["pass_at_1"], "B_pass@32": b["raw"]["pass_at_k"]}
    ge = all(got[c] >= bar[c]["value"] for c in got)
    gt = any(got[c] > bar[c]["value"] for c in got)
    return got, ("BEATS" if ge and gt else "FAILED")


CHALLENGER_PAIRS = [("v2_sft2", "v2_sft2-A", "v2_sft2-B"),
                    ("w4dgp", "w4dgp-A", "w4dgp-B"),
                    ("w4dgm", "w4dgm-A", "w4dgm-B")]


def render(arms, bar, frozen_sha):
    L = []
    L.append("# E2.c / Gate-2 ledger — the one table a retrain must beat")
    L.append("")
    L.append("Generated by `python3 tools/e2c_ledger.py`. Every number is recomputed")
    L.append("from the arm's append-only `rows.jsonl` with `harness.gate_check`")
    L.append("(keep-first dedup, `sample==\"corruption\"` excluded, pass@1 = the temp-0")
    L.append("greedy sample). summary.json is never read.")
    L.append("")
    L.append(f"Frozen baseline artifact: `corpus/e2c_baseline.json`, SHA-256 `{frozen_sha}`")
    L.append("(Amendment 13, Eric 2026-07-08 — unchanged).")
    L.append("")
    L.append("## The bar (frozen baseline arm: gpt-oss-120b)")
    L.append("")
    L.append("| cell | bar |")
    L.append("|---|---|")
    for c in ("A_pass@1", "A_pass@32", "B_pass@1", "B_pass@32"):
        L.append(f"| {c} | {bar[c]['value']}/{bar[c]['n']} |")
    L.append("")
    L.append("Gate-2 \"beats\" (Amendment 13): >= the bar in all four cells AND")
    L.append("strictly > in at least one, same holdout, same /23 framing-B denominator,")
    L.append("same seeds and MUTATIONS list, same frozen Amendment-12 budget.")
    L.append("")
    L.append("## Every measured arm")
    L.append("")
    L.append("| arm | model | framing | n | pass@1 | pass@32 | CLEAN floor @32 | audit | health |")
    L.append("|---|---|---|---|---|---|---|---|---|")
    for a in arms:
        floor = a.get("clean_floor")
        fl = f"{floor['pass_at_k']}" if floor else "—"
        audited = a.get("audited")
        pk = f"{a['raw']['pass_at_k']}"
        if audited:
            pk += f" (audited {audited['pass_at_k']})"
        health = "OK" if a["gate_check_ok"] else "**INVALID**"
        L.append(f"| {a['label']} | {a['model']} | {a['framing']} | {a['n_specs']} | "
                 f"{a['raw']['pass_at_1']} | {pk} | {fl} | {a['audit_status']} | {health} |")
    L.append("")
    L.append("## Verdicts against the bar")
    L.append("")
    L.append("| challenger | A pass@1 | A pass@32 | B pass@1 | B pass@32 | verdict |")
    L.append("|---|---|---|---|---|---|")
    for name, la, lb in CHALLENGER_PAIRS:
        got, v = verdict(arms, la, lb, bar)
        L.append(f"| {name} | {got['A_pass@1']} | {got['A_pass@32']} | "
                 f"{got['B_pass@1']} | {got['B_pass@32']} | **{v}** |")
    L.append("")
    L.append("Verdicts compare raw ledger counts in both columns, as Amendment 16 did.")
    L.append("No challenger has a completed manual Rule-9 triage, and Rule 9 can only")
    L.append("lower a count — so a FAILED verdict is safe and a BEATS verdict would")
    L.append("need the triage before it could be claimed.")
    L.append("")
    L.append("`w4dg` gets no verdict row: its framing-B arm covers 4 of the 23 specs,")
    L.append("so two of the four cells do not exist. `w4dgp`'s A cells come from a run")
    L.append("that fails gate-check (6.7% api_error); its verdict is FAILED on the B")
    L.append("cells alone, which are healthy.")
    L.append("")
    L.append("## Notes per arm")
    L.append("")
    for a in arms:
        extra = ""
        if not a["gate_check_ok"]:
            extra = " " + "; ".join(a["gate_check_failures"])
        floor = a.get("clean_floor")
        if floor and floor["unauditable_rows"]:
            extra += (f" {floor['unauditable_rows']} passing rows have a candidate"
                      f" sha256 that no longer matches the file on disk.")
        L.append(f"- **{a['label']}** (`{a['run_id']}`, Amendment {a['amendment']}): "
                 f"{a['note']}.{extra}")
    L.append("")
    return "\n".join(L)


def main():
    check = "--check" in sys.argv
    frozen, sha = frozen_baseline()
    if sha != FROZEN_BASELINE_SHA:
        print(f"FAIL: corpus/e2c_baseline.json sha256 {sha} != frozen "
              f"{FROZEN_BASELINE_SHA} (Amendment 13). The append-never baseline "
              f"was edited without a sign-off.", file=sys.stderr)
        return 1

    arms = build()
    bar = cells(arms)

    # the recomputed baseline must reproduce the frozen file, or the ledger lies
    fa = frozen["framing_A"]["gpt-oss-120b"]
    fb = frozen["framing_B"]["gpt-oss-120b"]
    expected = {"A_pass@1": fa["pass@1"], "A_pass@32": fa["pass@32"],
                "B_pass@1": fb["pass@1"], "B_pass@32": fb["pass@32"]}
    drift = {c: (bar[c]["value"], expected[c]) for c in expected
             if bar[c]["value"] != expected[c]}
    if drift:
        print(f"FAIL: re-scored baseline does not match the frozen file: {drift}",
              file=sys.stderr)
        return 1

    doc = {
        "_note": "Recomputed Gate-2 comparison table: the frozen E2.c baseline "
                 "(corpus/e2c_baseline.json, Amendment 13) plus every arm measured "
                 "against it. Regenerate with tools/e2c_ledger.py; verify with "
                 "--check. Derived artifact -- the baseline file stays frozen.",
        "frozen_baseline_sha256": sha,
        "holdout_sha256": frozen["holdout_sha256"],
        "budget": frozen["budget"],
        "bar": bar,
        "beats_definition": frozen["gate2_bar"]["beats_definition"],
        "arms": arms,
        "verdicts": {name: {"cells": verdict(arms, la, lb, bar)[0],
                            "verdict": verdict(arms, la, lb, bar)[1]}
                     for name, la, lb in CHALLENGER_PAIRS},
    }
    md = render(arms, bar, sha)

    if check:
        rc = 0
        for path, want in ((JSON_OUT, json.dumps(doc, indent=2) + "\n"), (MD_OUT, md)):
            if not path.exists():
                print(f"FAIL: {path} missing", file=sys.stderr)
                rc = 1
            elif path.read_text() != want:
                print(f"FAIL: {path} is stale -- rerun tools/e2c_ledger.py",
                      file=sys.stderr)
                rc = 1
        # every non-partial arm must pass its own health check
        for a in arms:
            if not a["gate_check_ok"] and a["label"] != "w4dgp-A":
                print(f"FAIL: {a['label']} fails gate-check unexpectedly",
                      file=sys.stderr)
                rc = 1
        if rc == 0:
            print("e2c-ledger: OK "
                  f"(baseline sha {sha[:12]}…, {len(arms)} arms re-scored)")
        return rc

    JSON_OUT.write_text(json.dumps(doc, indent=2) + "\n")
    MD_OUT.write_text(md)
    print(f"wrote {JSON_OUT}\nwrote {MD_OUT}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
