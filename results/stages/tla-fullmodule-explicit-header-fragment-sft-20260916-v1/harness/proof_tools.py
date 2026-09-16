"""TLAPS + Apalache harness hooks (W0.2 gate wiring).

Run: python3 -m harness.proof_tools  -> verifies both tools on known-good
examples through harness code paths and writes a ledger entry.
"""
import json
import shutil
import sys
from pathlib import Path

from .runner import REPO, check_apalache, check_tlapm

SMOKE = REPO / "tools" / "smoke"


def main():
    rundir = REPO / "results" / "runs" / "tools-smoke"
    logdir = rundir / "logs"
    logdir.mkdir(parents=True, exist_ok=True)
    work = Path("/tmp/prove-tla-toolsmoke")
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    for f in SMOKE.glob("*.tla"):
        shutil.copy(f, work / f.name)

    rows, ok = [], True
    st, proved, total, out, dt = check_tlapm(work / "ProofSmoke.tla", work)
    (logdir / "tlapm.log").write_text(out)
    rows.append({"tool": "tlapm", "example": "ProofSmoke.tla", "status": st,
                 "obligations": f"{proved}/{total}", "seconds": round(dt, 1)})
    ok &= (st == "pass")

    st, out, dt = check_apalache(work / "Counter.tla", work, inv="Inv")
    (logdir / "apalache.log").write_text(out)
    rows.append({"tool": "apalache", "example": "Counter.tla", "status": st,
                 "seconds": round(dt, 1)})
    ok &= (st == "pass")

    (rundir / "rows.jsonl").write_text("\n".join(json.dumps(r) for r in rows) + "\n")
    for r in rows:
        print(r)
    shutil.rmtree(work, ignore_errors=True)
    if not ok:
        print("TOOL VERIFICATION FAILED — Gate 0 checkbox not satisfied.")
        sys.exit(1)
    print("Both proof tools verified through the harness.")


main()
