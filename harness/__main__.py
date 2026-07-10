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
                   help="anthropic | anthropic:<model-id> | openai:<model-id> "
                        "(OPENAI_BASE_URL+OPENAI_API_KEY) | stub (default: stub)")
    p.add_argument("--n", type=int, default=None,
                   help="best-of-N override (default: repair_budget.json)")
    p.add_argument("--resume-from", default=None,
                   help="prior run-id whose completed specs (progress.jsonl) are skipped")
    s = sub.add_parser("semaudit", help="semantic-preservation audit of model repairs")
    s.add_argument("--corpus", default=DEFAULT_CORPUS)
    s.add_argument("--run-id", required=True)
    s.add_argument("--specs", default=None, help="comma-separated; default all winners")
    g = sub.add_parser("gate1-report", help="assemble GATE1_STATUS.md from arm run dirs")
    g.add_argument("--arms", required=True,
                   help="label=rundir[+rundir2],...  e.g. gpt-oss-120b=g1-sweep2-gptoss120b+g1-sweep2r-gptoss120b")
    g.add_argument("--out", default="GATE1_STATUS.md")
    e = sub.add_parser("gen-eval", help="E2.c Gate-2 baseline: generation (A) and repair (B) framings")
    e.add_argument("--framing", required=True, choices=["A", "B"])
    e.add_argument("--model", required=True,
                   help="openai:<model-id> (OPENAI_BASE_URL+OPENAI_API_KEY[_CMD]) | "
                        "anthropic | anthropic:<model-id> | local-stub (zero-spend dry run)")
    e.add_argument("--run-id", required=True)
    e.add_argument("--k", type=int, default=32, help="samples at temp 0.8 for pass@k (frozen budget: 32)")
    e.add_argument("--specs", default=None, help="comma-separated holdout spec numbers; default all 30")
    e.add_argument("--corpus-data", default="/Users/eric/GitHub/tla_benchmark/data")
    e.add_argument("--no-resume", action="store_true",
                   help="ignore any existing rows.jsonl and redo every (spec, sample)")
    pt = sub.add_parser("proof-traces", help="W2.4 obligation-trace bootstrap (tlapm sweep)")
    pt.add_argument("--source", required=True, choices=["corpus", "examples"])
    pt.add_argument("--out", required=True, help="output dir under results/proof_traces/...")
    pt.add_argument("--corpus", default=DEFAULT_CORPUS)
    pt.add_argument("--examples-dir", default=str(Path(__file__).resolve().parent.parent
                                                   / "tools" / "tlaplus-examples"))
    pt.add_argument("--timeout", type=int, default=600)
    pt.add_argument("--limit", type=int, default=None,
                     help="cap number of modules attempted (examples source; debug/partial runs)")
    a = ap.parse_args()
    specs = list(dict.fromkeys(a.specs.split(","))) if getattr(a, "specs", None) else None
    if a.cmd == "gen-eval":
        from .gen_eval import run_gen_eval
        run_gen_eval(Path(a.corpus_data), a.run_id, a.framing, a.model, a.k,
                    specs=specs, resume=not a.no_resume)
    elif a.cmd == "repair":
        from .repair import run_repair
        # repair preserves the given --specs order (informative specs first =
        # cheap restarts; STAGE1_STRATEGY.md); `run` still treats it as a filter
        run_repair(Path(a.corpus), a.run_id, a.model, specs=specs, n=a.n,
                   resume_from=a.resume_from)
    elif a.cmd == "proof-traces":
        from .proof_traces_cli import run_proof_traces_cli
        run_proof_traces_cli(a.source, Path(a.out), Path(a.corpus), Path(a.examples_dir),
                              timeout=a.timeout, limit=a.limit)
    elif a.cmd == "semaudit":
        from .semaudit import run_semaudit
        run_semaudit(Path(a.corpus), a.run_id, specs=specs)
    elif a.cmd == "gate1-report":
        from .gate1_report import run_report
        run_report(a.arms, a.out)
    else:
        run_sweep(Path(a.corpus), a.run_id, a.stages.split(","), specs=specs,
                  timeout=a.timeout, jobs=a.jobs, extra_cfg_dir=a.extra_cfg_dir)


main()
