"""Stage 2 of the lint-repair probe: do the now-PARSING candidates actually CHECK?

lint_repair_probe.py showed 88 candidates from 9 of the 15 framing-A-unsolved
specs parse after deterministic lint. Parsing is necessary but not sufficient --
this stage runs the harness's real scoring path (sany + tlc + tlaps, same
timeouts) on the linted text and reports how many specs would flip to solved.

A pass here means "model output + deterministic lint" is checkable. That is a
legitimate loop-side result under the north-star (correctness from the verify
LOOP, not the weights) -- but it is NOT the same claim as the model emitting a
correct spec unaided, and must never be merged into a frozen arm's rows.jsonl.
Everything here writes to a scratch run dir.
"""
import json
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from harness.gen_eval import _score  # noqa: E402
from harness.runner import build_module_index  # noqa: E402
from tools.lint_repair_probe import lint  # noqa: E402

REPO = Path(__file__).resolve().parents[1]
RUN = REPO / "results" / "runs" / "gate2-w4dg-120b-A"
SCRATCH = Path("/tmp/prove-tla-lint-probe")


def main():
    cfg = json.loads((RUN / "config.json").read_text())
    corpus = Path(cfg["corpus"])
    probe = json.loads((RUN / "lint_probe.json").read_text())
    recovered = [r for r in probe["results"]
                 if r.get("after") == "pass" and r.get("before") != "pass"]
    print(f"now-parsing candidates to check with TLC: {len(recovered)}")

    num2mod, mod2path = build_module_index(corpus)
    cfg_dirs = [("override", REPO / "corpus" / "configs" / "overrides"),
                ("original", corpus / "cfg"),
                ("draft", REPO / "corpus" / "configs" / "drafts")]
    workroot = SCRATCH / "work"
    logdir = SCRATCH / "logs"
    logdir.mkdir(parents=True, exist_ok=True)

    by_spec = defaultdict(list)
    for r in recovered:
        by_spec[r["cand"].split("-")[0]].append(r["cand"])

    out = []
    flipped = []
    for spec in sorted(by_spec, key=int):
        spec_verdicts = []
        for name in by_spec[spec]:
            src = (RUN / "candidates" / name).read_text(errors="replace")
            fixed, _ = lint(src)
            try:
                _row, verdict, _log = _score(
                    spec, fixed, corpus, num2mod, mod2path, cfg_dirs,
                    workroot, logdir, 120, log_name=f"lint-{name}")
            except Exception as e:  # noqa: BLE001
                verdict = f"probe_error:{type(e).__name__}"
            spec_verdicts.append(verdict)
            out.append({"spec": spec, "cand": name, "verdict_after_lint": verdict})
            if verdict == "pass":
                break  # pass@k reached for this spec; stop burning TLC time
        mark = "PASS" if "pass" in spec_verdicts else "still fails"
        if "pass" in spec_verdicts:
            flipped.append(spec)
        print(f"  spec {spec:>3}: {mark}  ({len(spec_verdicts)} checked) "
              f"{sorted(set(spec_verdicts))[:3]}")

    (RUN / "lint_probe_tlc.json").write_text(json.dumps(
        {"rows": out, "flipped_specs": flipped}, indent=2))
    print(f"\nspecs that flip unsolved -> solved with lint: {len(flipped)} {flipped}")
    print(f"framing A: 15/30 unaided  ->  {15 + len(flipped)}/30 with deterministic lint")
    print(f"wrote {RUN / 'lint_probe_tlc.json'}")


if __name__ == "__main__":
    main()
