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
    le = sub.add_parser("loop-eval", help="framing L: verifier IN the loop at framing-A's model-call budget")
    le.add_argument("--model", required=True,
                    help="openai:<model-id> (OPENAI_BASE_URL+OPENAI_API_KEY[_CMD]) | "
                         "anthropic | anthropic:<model-id> | local-stub")
    le.add_argument("--run-id", required=True)
    le.add_argument("--chains", type=int, default=8, help="independent restarts (frozen budget: 8)")
    le.add_argument("--rounds", type=int, default=4, help="calls per chain: 1 generate + N-1 repairs (frozen budget: 4)")
    le.add_argument("--specs", default=None, help="comma-separated holdout spec numbers; default all 30")
    le.add_argument("--corpus-data", default="/Users/eric/GitHub/tla_benchmark/data")
    le.add_argument("--no-resume", action="store_true")
    gc = sub.add_parser("gate-check", help="recompute pass@k from rows.jsonl; fail hard on api_error/extraction defects (never trust summary.json)")
    gc.add_argument("run_dirs", nargs="+", help="run dir(s) containing rows.jsonl")
    gc.add_argument("--max-api-error-rate", type=float, default=0.05)
    gc.add_argument("--max-unextracted-rate", type=float, default=0.90)
    mr = sub.add_parser("mutation-recall",
                        help="measure the mutation battery's operator recall against a "
                             "localized reference probe set; fail below the floor")
    mr.add_argument("ledgers", nargs="+", help="w2_survivors.jsonl ledger(s)")
    mr.add_argument("--limit", type=int, default=12, help="specs sampled (reproducible)")
    mr.add_argument("--min-recall", type=float, default=0.5)
    mr.add_argument("--timeout", type=int, default=60)
    mr.add_argument("--seed", type=int, default=0)
    mr.add_argument("--out", default=None, help="write the report as JSON")
    rp = sub.add_parser("replay", help="re-run one ledgered sample at its recorded "
                                       "decoder seed and diff against the stored candidate")
    rp.add_argument("run_dir", help="results/runs/<run-id> containing rows.jsonl")
    rp.add_argument("--spec", required=True)
    rp.add_argument("--sample", required=True, help='"greedy" or a sample index')
    rp.add_argument("--framing", default=None, choices=["A", "B"],
                    help="required only if the pair exists in both framings")
    rp.add_argument("--corpus-data", default=None,
                    help="default: the corpus recorded in the run's config.json")
    rp.add_argument("--model", default=None,
                    help="default: openai:<model id recorded on the row>")
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
    elif a.cmd == "loop-eval":
        from .loop_eval import run_loop_eval
        run_loop_eval(Path(a.corpus_data), a.run_id, a.model, chains=a.chains,
                      rounds=a.rounds, specs=specs, resume=not a.no_resume)
    elif a.cmd == "repair":
        from .repair import run_repair
        # repair preserves the given --specs order (informative specs first =
        # cheap restarts; STAGE1_STRATEGY.md); `run` still treats it as a filter
        run_repair(Path(a.corpus), a.run_id, a.model, specs=specs, n=a.n,
                   resume_from=a.resume_from)
    elif a.cmd == "replay":
        from .replay import run_replay_cli
        raise SystemExit(run_replay_cli(a.run_dir, a.spec, a.sample, a.framing,
                                        a.corpus_data, a.model))
    elif a.cmd == "gate-check":
        from .gate_check import main as gate_check_main
        raise SystemExit(gate_check_main(a.run_dirs, a.max_api_error_rate,
                                         a.max_unextracted_rate))
    elif a.cmd == "mutation-recall":
        from .mutation_recall import main as mutation_recall_main
        raise SystemExit(mutation_recall_main(a.ledgers, a.limit, a.min_recall,
                                              a.timeout, a.seed, a.out))
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
