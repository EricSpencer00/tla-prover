"""TLAPS + Apalache harness hooks (W0.2 gate wiring).

Run: python3 -m harness.proof_tools  -> verifies both tools on known-good
examples through harness code paths and writes a ledger entry.
"""
import json
import re
import shutil
import sys
from pathlib import Path

from .runner import REPO, run_cmd

TLAPM = REPO / "tools" / "tlapm" / "bin" / "tlapm"
APALACHE = REPO / "tools" / "apalache-0.58.2" / "bin" / "apalache-mc"
SMOKE = REPO / "tools" / "smoke"


def check_tlapm(tla_file: Path, workdir: Path, timeout=300):
    """Returns (status, proved, total, output). pass = all obligations proved."""
    rc, out, dt, timed_out = run_cmd([str(TLAPM), tla_file.name], workdir, timeout)
    if timed_out:
        return "timeout", 0, 0, out, dt
    m = re.search(r"All (\d+) obligations? proved", out)
    if m:
        n = int(m.group(1))
        return "pass", n, n, out, dt
    mm = re.search(r"(\d+)/(\d+) obligations? proved", out)
    if mm:
        return "partial", int(mm.group(1)), int(mm.group(2)), out, dt
    return "error", 0, 0, out, dt


def check_apalache(tla_file: Path, workdir: Path, inv=None, length=5, timeout=300):
    """Returns (status, output). pass = 'The outcome is: NoError'."""
    cmd = [str(APALACHE), "check", f"--length={length}"]
    if inv:
        cmd.append(f"--inv={inv}")
    cmd.append(tla_file.name)
    rc, out, dt, timed_out = run_cmd(cmd, workdir, timeout)
    if timed_out:
        return "timeout", out, dt
    if "The outcome is: NoError" in out:
        return "pass", out, dt
    if "The outcome is: Error" in out:
        return "fail_violation", out, dt
    return "error", out, dt


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
