"""CLI glue for `python3 -m harness proof-traces` (W2.4). Discovers the module
list per --source and calls proof_traces.run_proof_traces; writes config.json
and summary.json (Rule 8) in the given --out dir.

corpus source: the PROOF_MODULES population (corpus/configs/populations.json)
plus the TLAPS stdlib's own *_proofs.tla library modules (Amendment 8 names
both explicitly: "the corpus's TLAPS proof modules ... the TLAPS library
specs" per PLAN.md ledger entry 8 prose in the task brief). Deps are resolved
via runner.build_module_index/local_deps so EXTENDS-only siblings (e.g. 67's
EWD840_proof EXTENDS EWD840) get staged into the same workdir.

examples source: every tlaplus/examples .tla file containing a THEOREM/LEMMA/
COROLLARY/PROPOSITION with a PROOF or a terminal BY (heuristic: tlapm will
just report no_obligations on any false positive, which is itself a valid
recorded row, so the filter only needs to be cheap, not exact). Deps are
whatever other .tla files live in the same directory (examples specs keep
their deps as siblings, not a flat pool) -- copying the whole directory's
.tla siblings into the workdir mirrors how a user would open that spec.
"""
import json
import re
import time
from pathlib import Path

from .proof_traces import run_proof_traces, backend_discharge_rates
from .runner import REPO, build_module_index, local_deps

PROOF_STDLIB = REPO / "tools" / "tlapm" / "lib" / "tlapm" / "stdlib"


def _transitive_local_deps(text: str, mod: str, mod2path: dict):
    """Transitive closure of corpus-local EXTENDS/INSTANCE deps (mirrors
    runner._write_local_deps' traversal, without the repair-patch lookup --
    proof-trace harvesting scores the canonical corpus text, not a model's
    repair, so there is no patch to prefer). Needed because tlapm resolves by
    module name and a two-hop chain (e.g. corpus 67 EXTENDS 65/EWD840, which
    itself INSTANCEs 68/SyncTerminationDetection) is otherwise silently
    dropped -- found empirically 2026-07-08 when a non-transitive lookup left
    67's build missing SyncTerminationDetection.tla."""
    seen = set()
    frontier = local_deps(text, mod2path) - seen
    while frontier:
        d = frontier.pop()
        if d in seen or d == mod:
            continue
        seen.add(d)
        dtext = mod2path[d].read_text(errors="replace")
        frontier |= (local_deps(dtext, mod2path) - seen)
    return seen


def _corpus_modules(corpus: Path):
    pop_file = REPO / "corpus" / "configs" / "populations.json"
    pop = json.loads(pop_file.read_text()) if pop_file.exists() else {}
    proof_nums = pop.get("proof_module", [])

    num2mod, mod2path = build_module_index(corpus)
    modules = []
    for num in proof_nums:
        f = corpus / "tla_files" / f"{num}.tla"
        if not f.exists():
            continue
        text = f.read_text(errors="replace")
        mod = num2mod.get(num)
        deps = _transitive_local_deps(text, mod, mod2path)
        dep_paths = [mod2path[d] for d in deps if d in mod2path]
        modules.append((f"corpus-{num}", f, dep_paths))

    # TLAPS stdlib's own proof libraries (*_proofs.tla) -- Amendment 8's "TLAPS
    # library specs". Each is self-contained within the stdlib dir, already on
    # tlapm's -I search path, so no extra deps need staging.
    if PROOF_STDLIB.exists():
        for f in sorted(PROOF_STDLIB.glob("*_proofs.tla")):
            modules.append((f"stdlib-{f.stem}", f, []))
    return modules


THEOREM_PROOF_RE = re.compile(
    r"^\s*(THEOREM|LEMMA|COROLLARY|PROPOSITION)\b.*?\n(?:.*\n){0,3}?\s*(PROOF|BY\b|<1>)",
    re.M)


def _looks_provable(text: str):
    return bool(re.search(r"^\s*(THEOREM|LEMMA|COROLLARY|PROPOSITION)\b", text, re.M)) \
        and bool(re.search(r"\bPROOF\b|^\s*<\d+>|^\s*BY\b", text, re.M))


def _examples_modules(examples_dir: Path, limit=None):
    modules = []
    if not examples_dir.exists():
        return modules
    for f in sorted(examples_dir.rglob("*.tla")):
        try:
            text = f.read_text(errors="replace")
        except OSError:
            continue
        if not _looks_provable(text):
            continue
        siblings = [s for s in f.parent.glob("*.tla") if s != f]
        mid = "examples-" + str(f.relative_to(examples_dir)).replace("/", "__")
        modules.append((mid, f, siblings))
        if limit and len(modules) >= limit:
            break
    return modules


def run_proof_traces_cli(source: str, out: Path, corpus: Path, examples_dir: Path,
                          timeout=600, limit=None):
    if source == "corpus":
        modules = _corpus_modules(corpus)
    else:
        modules = _examples_modules(examples_dir, limit=limit)

    out.mkdir(parents=True, exist_ok=True)
    config = {
        "source": source,
        "timeout_s": timeout,
        "limit": limit,
        "modules_discovered": len(modules),
        "reproduction_cmd": (
            f"python3 -m harness proof-traces --source {source} --out {out} "
            f"--timeout {timeout}" + (f" --limit {limit}" if limit else "")
        ),
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    (out / "config.json").write_text(json.dumps(config, indent=2))

    t0 = time.time()
    summary = run_proof_traces(out, source, modules, timeout=timeout)
    summary["seconds_total"] = round(time.time() - t0, 1)
    summary["backend_discharge_rates"] = backend_discharge_rates(out / "rows.jsonl")
    (out / "summary.json").write_text(json.dumps(summary, indent=2))
    print(json.dumps({k: v for k, v in summary.items() if k != "module_rows"}, indent=2))
    return summary
