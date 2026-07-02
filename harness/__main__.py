"""CLI: python3 -m harness run --run-id oracle-v0 [--specs 1,2,3] [--stages sany,tlc]"""
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
    a = ap.parse_args()
    specs = set(a.specs.split(",")) if a.specs else None
    run_sweep(Path(a.corpus), a.run_id, a.stages.split(","), specs=specs,
              timeout=a.timeout, jobs=a.jobs, extra_cfg_dir=a.extra_cfg_dir)


main()
