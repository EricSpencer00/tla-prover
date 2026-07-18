"""W4 cross-family verification CLI: verify ONE candidate (nl, spec, cfg,
invariant) through the EXACT W2 gate stack (fidelity contract, SANY,
non-vacuous TLC, mutation battery, decontam) and print the verdict row as
JSON. Used by teacher agents (Claude/Opus etc.) that generate candidates and
iterate locally until the gates pass -- the verifier is the same code the
gpt-oss funnel uses, so cross-family survivors are gate-identical.

Usage:
  python3 -m harness.w4_verify_cell --nl nl.txt --spec spec.tla --cfg spec.cfg \
      --invariant NonNegative --workdir /tmp/cellwork
Exit 0 with {"survived": true, ...} on stdout iff every gate passes.
"""
import argparse
import json
import sys
from pathlib import Path

from .w2_loop import decontam_survivor, run_loop_for_seed
from .w21_funnel import load_canonical
from .runner import module_name


class _OneShot:
    id = "teacher-candidate"

    def __init__(self, reply):
        self.reply = reply
        self.calls = 0

    def generate(self, prompt, n, temperature, max_tokens):
        self.calls += 1
        if self.calls > 1:
            raise AssertionError("one-shot verifier: no repair iterations here")
        return [self.reply]


def main(argv=None):
    ap = argparse.ArgumentParser(prog="python3 -m harness.w4_verify_cell")
    ap.add_argument("--nl", required=True)
    ap.add_argument("--spec", required=True)
    ap.add_argument("--cfg", required=True)
    ap.add_argument("--invariant", required=True)
    ap.add_argument("--workdir", required=True)
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--skip-decontam", action="store_true")
    a = ap.parse_args(argv)

    nl = Path(a.nl).read_text()
    spec = Path(a.spec).read_text()
    cfg = Path(a.cfg).read_text()
    reply = f"```tla\n{spec}\n```\n```cfg\n{cfg}\n```\nPROPERTY_INVARIANT: {a.invariant}\n"
    wd = Path(a.workdir).resolve()   # ABSOLUTE: java.io.tmpdir trap
    wd.mkdir(parents=True, exist_ok=True)
    mod = module_name(spec) or "Unknown"
    r = run_loop_for_seed(_OneShot(reply), nl, mod, wd, timeout=a.timeout, max_iters=1)
    if r["survived"] and not a.skip_decontam:
        verdict, score = decontam_survivor(r["spec_text"], load_canonical())
        if verdict != "clean":
            r = {**r, "survived": False, "rejection_reason": f"decontam:{score:.2f}"}
    print(json.dumps(r))
    sys.exit(0 if r["survived"] else 1)


if __name__ == "__main__":
    main()
