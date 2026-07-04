"""CLI: python3 -m harness run --run-id oracle-v0 [--specs 1,2,3] [--stages sany,tlc]
     python3 -m harness repair --run-id w11-x --specs 92,78 --model stub --n 4"""
import argparse
from pathlib import Path

from .runner import run_sweep

DEFAULT_CORPUS = "/Users/eric/GitHub/tla_benchmark/data"


def main():
    ap = argparse.ArgumentParser(prog="harness")
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--corpus", default=DEFAULT_CORPUS)
    r.add_argument("--run-id", required=True)
    r.add_argument("--stages", default="sany,tlc")
    r.add_argument("--specs", default=None, help="comma-separated spec numbers; default all")
    r.add_argument("--timeout", type=int, default=120)
    r.add_argument("--jobs", type=int, default=6)
    r.add_argument("--extra-cfg-dir", default=None, help="fallback dir for drafted .cfg files")
    p = sub.add_parser("repair", help="Stage-1 repair agent (W1.1)")
    p.add_argument("--corpus", default=DEFAULT_CORPUS)
    p.add_argument("--run-id", required=True)
    p.add_argument("--specs", default=None, help="comma-separated spec numbers; default all")
    p.add_argument("--model", default="stub",
                   help="anthropic | anthropic:<model-id> | stub (default: stub)")
    p.add_argument("--n", type=int, default=None,
                   help="best-of-N override (default: repair_budget.json)")
    a = ap.parse_args()
    specs = set(a.specs.split(",")) if a.specs else None
    if a.cmd == "repair":
        from .repair import run_repair
        run_repair(Path(a.corpus), a.run_id, a.model, specs=specs, n=a.n)
    else:
        run_sweep(Path(a.corpus), a.run_id, a.stages.split(","), specs=specs,
                  timeout=a.timeout, jobs=a.jobs, extra_cfg_dir=a.extra_cfg_dir)


main()
