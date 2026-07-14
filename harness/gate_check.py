"""gate-check: recompute pass@k from a run's append-only rows.jsonl and
fail hard on run-health defects that have historically corrupted results.

Motivation (2026-07-14 Gate-2 framing-B postmortem): the serve had
--max-model-len 4096 while repair prompts ran 4.4k-17k tokens; 99% of the
lost-spec attempts were api_error 400s, but the run completed "green" and
summary.json went stale. Rule since then: NEVER trust summary.json; re-score
from rows.jsonl. This module makes that rule executable and adds fail-fast
thresholds so a config-broken run dies loudly instead of producing a
plausible-looking regression.

Checks (all computed from rows.jsonl only, scoring logic identical to the
frozen ledger re-score: verdict=="pass", exclude sample=="corruption"):
  - api_error_rate  > threshold (default 0.05) -> FAIL
  - no_module_extracted rate > threshold (default 0.90) -> FAIL (a server
    returning garbage/empty on every call looks like a 0-pass model)
  - zero scored rows -> FAIL
"""
import json
import sys
from collections import defaultdict
from pathlib import Path


def load_rows(run_dir: Path) -> list[dict]:
    rows_path = Path(run_dir) / "rows.jsonl"
    if not rows_path.exists():
        raise FileNotFoundError(f"no rows.jsonl in {run_dir}")
    rows = []
    for line in rows_path.read_text().splitlines():
        line = line.strip()
        if line:
            rows.append(json.loads(line))
    return rows


def gate_check(run_dir, max_api_error_rate=0.05, max_unextracted_rate=0.90) -> dict:
    """Recompute pass@k and run-health stats from rows.jsonl. Returns a report
    dict with report["ok"] False if any health threshold trips."""
    rows = load_rows(Path(run_dir))
    scored = [r for r in rows if r.get("sample") != "corruption"]
    n = len(scored)
    by_spec: dict = defaultdict(list)
    for r in scored:
        by_spec[str(r["spec"])].append(r)

    passed = sorted(s for s, rs in by_spec.items()
                    if any(r.get("verdict") == "pass" for r in rs))
    pass1 = sorted(s for s, rs in by_spec.items()
                   if rs and sorted(rs, key=lambda r: str(r["sample"]))[0].get("verdict") == "pass")
    n_api_err = sum(1 for r in scored if r.get("verdict") == "api_error")
    n_unext = sum(1 for r in scored if r.get("verdict") == "no_module_extracted")

    failures = []
    if n == 0:
        failures.append("zero scored rows")
    else:
        if n_api_err / n > max_api_error_rate:
            failures.append(f"api_error rate {n_api_err}/{n} = {n_api_err/n:.1%} "
                            f"> {max_api_error_rate:.0%} -- serve/client config is "
                            f"broken (ctx limit? auth? endpoint?); results INVALID")
        if n_unext / n > max_unextracted_rate:
            failures.append(f"no_module_extracted rate {n_unext}/{n} = {n_unext/n:.1%} "
                            f"> {max_unextracted_rate:.0%} -- model output unusable "
                            f"(template/channel breakage?)")

    return {
        "run_dir": str(run_dir),
        "rows_total": len(rows),
        "rows_scored": n,
        "specs": len(by_spec),
        "pass_at_k": len(passed),
        "pass_at_1": len(pass1),
        "pass_set": passed,
        "api_error_rows": n_api_err,
        "no_module_extracted_rows": n_unext,
        "failures": failures,
        "ok": not failures,
    }


def main(run_dirs, max_api_error_rate=0.05, max_unextracted_rate=0.90) -> int:
    rc = 0
    for d in run_dirs:
        rep = gate_check(d, max_api_error_rate, max_unextracted_rate)
        print(f"\n== gate-check {rep['run_dir']} ==")
        print(f"rows={rep['rows_total']} scored={rep['rows_scored']} specs={rep['specs']}")
        print(f"pass@k = {rep['pass_at_k']}/{rep['specs']}  pass@1 = {rep['pass_at_1']}/{rep['specs']}")
        print(f"pass set: {rep['pass_set']}")
        print(f"api_error rows: {rep['api_error_rows']}  no_module_extracted: {rep['no_module_extracted_rows']}")
        if rep["ok"]:
            print("GATE-CHECK: OK")
        else:
            rc = 1
            for f in rep["failures"]:
                print(f"GATE-CHECK FAIL: {f}", file=sys.stderr)
    return rc
