"""W3.2: prompt-only proof-generation loop (PLAN.md W3.2, reframed under
Amendment 17 -- fine-tuning shelved, correctness comes from the tlapm
verifier, not the weights).

Iteration 1 asks the model for a complete TLA+ proof of the manifest's named
theorem, given the module text and top-k retrieval exemplars (harness/
proof_retrieval.py's query() over results/analysis/proof_retrieval_index.jsonl:
similar proved obligations plus their winning backend + BY facts). The
reply's proof block is spliced into the module immediately after the
THEOREM/LEMMA statement and tlapm is run (harness.runner.check_tlapm). On
failure, iteration n+1 feeds back the tail of the tlapm output (the failed/
omitted obligation snippets) plus fresh retrieval hits queried against that
failure text. Certification uses harness.lmgpa_bench.theorem_certified's
criterion: total obligations > 0, zero failed/omitted (status == "pass" with
proved == total), and the target theorem's own source span actually carries
the proof body (not a helper lemma masking an unproved target).

CLI: python3 -m harness.proof_gen run --manifest corpus/lmgpa/manifest.json \
    --model openai:<id> --run-id <id> [--limit N] [--k-iters 4]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

from .lmgpa_bench import DEFAULT_LMGPA_ROOT, MANIFEST_PATH, load_manifest, theorem_has_proof
from .proof_retrieval import query as retrieval_query
from .runner import check_tlapm

DEFAULT_INDEX_PATH = Path("results/analysis/proof_retrieval_index.jsonl")
DEFAULT_K_ITERS = 4
DEFAULT_RETRIEVAL_K = 5
TLAPM_TAIL_CHARS = 3000

_THEOREM_DECL_RE_TMPL = r"(THEOREM|LEMMA)(\s+{name}\s*==.*?)(\n(?:THEOREM|LEMMA)\s+\w|\n[-=]{{4,}}|\Z)"

_PROOF_FENCE_RE = re.compile(r"```(?:tla|tlaplus|tla\+)?\s*\n(.*?)```", re.DOTALL | re.IGNORECASE)
_PROOF_START_RE = re.compile(r"^\s*(PROOF\b|<\d+>|BY\b|OBVIOUS\b|OMITTED\b)")


# ---------------------------------------------------------------------------
# extraction / splicing
# ---------------------------------------------------------------------------

def extract_proof_block(reply: str) -> str | None:
    """Pull a spliceable TLA+ proof out of a model reply.

    Prefers a fenced ```tla ... ``` block; falls back to scanning the raw
    reply for the first line that looks like the start of a proof (PROOF,
    a <n>-step label, BY, or OBVIOUS) and taking everything from there to
    the end of the reply. Returns None if nothing proof-shaped is found."""
    if not reply:
        return None

    fence = _PROOF_FENCE_RE.search(reply)
    if fence:
        candidate = fence.group(1).strip()
        if candidate and _looks_like_proof(candidate):
            return candidate
        # a fenced block that isn't proof-shaped still might contain one
        # (e.g. model fenced the whole module) -- fall through to raw scan.

    lines = reply.split("\n")
    for i, line in enumerate(lines):
        if _PROOF_START_RE.match(line):
            candidate = "\n".join(lines[i:]).strip()
            if candidate:
                return candidate
    return None


def _looks_like_proof(text: str) -> bool:
    first_line = text.strip().split("\n", 1)[0]
    return bool(_PROOF_START_RE.match(first_line))


def splice_proof(module_text: str, theorem_name: str, proof_block: str) -> str:
    """Insert `proof_block` immediately after the named THEOREM/LEMMA's `==`
    statement, replacing any existing proof body that theorem already had.
    Raises ValueError if the theorem declaration can't be located."""
    pattern = re.compile(
        _THEOREM_DECL_RE_TMPL.format(name=re.escape(theorem_name)), re.DOTALL)
    m = pattern.search(module_text)
    if not m:
        raise ValueError(f"theorem {theorem_name!r} not found in module text")

    kind, body, tail_marker = m.group(1), m.group(2), m.group(3)
    # body is "<ws> Name == <expr...>" possibly already followed by a proof;
    # keep only the statement up to (not including) any existing proof
    # keywords, then append the fresh proof block.
    stmt_match = re.match(r"(.*?==.*?)(?:\n\s*(?:PROOF\b|<\d+>|BY\b|OBVIOUS\b|OMITTED\b).*)?\Z",
                           body, re.DOTALL)
    stmt = stmt_match.group(1).rstrip() if stmt_match else body.rstrip()

    new_decl = f"{kind}{stmt}\n{proof_block.strip()}\n"
    start, end = m.span()
    return module_text[:start] + new_decl + module_text[end - len(tail_marker):]


# ---------------------------------------------------------------------------
# prompt construction
# ---------------------------------------------------------------------------

def _format_hits(hits: list[dict]) -> str:
    if not hits:
        return "(no retrieval hits)"
    lines = []
    for i, h in enumerate(hits, 1):
        by_facts = ", ".join(h.get("by_facts") or []) or "(none recorded)"
        lines.append(
            f"[{i}] backend={h.get('backend')} score={h.get('score', 0):.3f}\n"
            f"    goal: {h.get('goal_text_normalized', '')[:300]}\n"
            f"    by_facts: {by_facts}")
    return "\n".join(lines)


def build_proof_prompt(module_text: str, theorem_name: str, retrieval_hits: list[dict],
                        error_evidence: str | None = None) -> str:
    """Build the model prompt for one proof-gen iteration. `error_evidence`,
    when given, is the tail of a prior failed tlapm run appended as feedback
    (iteration 2+)."""
    parts = [
        "You are proving a theorem in TLA+ using TLAPS (the TLA+ proof "
        "system). Write a complete, correct proof for the theorem named "
        f"{theorem_name!r} in the module below.",
        "",
        "Prefer a hierarchical proof (<1>-step structure) ending in QED "
        "when the theorem is non-trivial; OBVIOUS or a single BY is fine "
        "if it truly suffices.",
        "",
        "===BEGIN MODULE===",
        module_text,
        "===END MODULE===",
        "",
        "Similar previously-proved obligations (with the backend that "
        "discharged them and their BY facts), for context:",
        _format_hits(retrieval_hits),
    ]
    if error_evidence:
        parts += [
            "",
            "Your previous attempt did NOT certify. tlapm reported "
            "(tail of output):",
            "===BEGIN TLAPM OUTPUT===",
            error_evidence,
            "===END TLAPM OUTPUT===",
            "",
            "Revise the proof to address these failures.",
        ]
    parts += [
        "",
        f"Reply with ONLY the proof block for {theorem_name!r} (starting "
        "with PROOF, a <1> step, BY, or OBVIOUS), in a ```tla fenced code "
        "block. Do not repeat the THEOREM statement or the rest of the "
        "module.",
    ]
    return "\n".join(parts)


# ---------------------------------------------------------------------------
# per-theorem iterate-splice-certify loop
# ---------------------------------------------------------------------------

def _read_done_ids(rows_path: Path) -> set[str]:
    done = set()
    if rows_path.exists():
        with rows_path.open() as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    row = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if row.get("certified"):
                    done.add(row["id"])
    return done


def _tail(text: str, n: int = TLAPM_TAIL_CHARS) -> str:
    return text[-n:] if text and len(text) > n else (text or "")


def run_one_theorem(model, entry: dict, lmgpa_root: Path, index, run_dir: Path,
                     k_iters: int = DEFAULT_K_ITERS, retrieval_k: int = DEFAULT_RETRIEVAL_K,
                     timeout: int = 300, checker=check_tlapm) -> list[dict]:
    """Run the iterate-splice-certify loop for a single manifest entry.
    Returns the list of per-iteration ledger rows (also appended to
    run_dir/rows.jsonl by the caller). Persists the winning proof's module
    text to run_dir/proofs/<id>.tla on first certification."""
    module_path = lmgpa_root / entry["module_file"]
    original_text = module_path.read_text(errors="replace")
    theorem_name = entry["theorem_name"]

    workdir = run_dir / "work" / entry["id"]
    workdir.mkdir(parents=True, exist_ok=True)

    rows = []
    error_evidence = None
    query_text = theorem_name

    for it in range(1, k_iters + 1):
        hits = retrieval_query(index, query_text, k=retrieval_k) if index is not None else []
        prompt = build_proof_prompt(original_text, theorem_name, hits, error_evidence)
        replies = model.generate(prompt, n=1, temperature=0.2, max_tokens=2000)
        reply = replies[0] if replies else ""

        proof_block = extract_proof_block(reply)
        row = {"id": entry["id"], "iter": it, "certified": False,
               "proved": 0, "total": 0, "tlapm_status": "no_proof_block",
               "proof_sha": None}

        if proof_block is None:
            rows.append(row)
            error_evidence = "[no proof block extracted from model reply]"
            continue

        try:
            spliced = splice_proof(original_text, theorem_name, proof_block)
        except ValueError as e:
            row["tlapm_status"] = f"splice_error: {e}"
            rows.append(row)
            error_evidence = str(e)
            continue

        candidate_path = workdir / Path(entry["module_file"]).name
        candidate_path.write_text(spliced)
        status, proved, total, out, _dt = checker(candidate_path, workdir, timeout=timeout)

        certified = (status == "pass" and total > 0 and proved == total
                     and theorem_has_proof(spliced, theorem_name))

        row.update({
            "certified": certified,
            "proved": proved,
            "total": total,
            "tlapm_status": status,
            "proof_sha": hashlib.sha256(proof_block.encode()).hexdigest(),
        })
        rows.append(row)

        if certified:
            proofs_dir = run_dir / "proofs"
            proofs_dir.mkdir(parents=True, exist_ok=True)
            (proofs_dir / f"{entry['id']}.tla").write_text(spliced)
            break

        error_evidence = _tail(out)
        query_text = error_evidence or theorem_name

    return rows


def run_proof_gen(model, manifest_path: Path = MANIFEST_PATH, run_dir: Path = None,
                   k_iters: int = DEFAULT_K_ITERS, limit: int | None = None,
                   index_path: Path = DEFAULT_INDEX_PATH,
                   lmgpa_root: Path = DEFAULT_LMGPA_ROOT, timeout: int = 300,
                   checker=check_tlapm) -> dict:
    """Drive run_one_theorem across the manifest, resumable per theorem id
    (ids already certified in run_dir/rows.jsonl are skipped). Appends every
    attempt row to run_dir/rows.jsonl and prints a running certified tally."""
    if run_dir is None:
        raise ValueError("run_dir is required")
    run_dir = Path(run_dir)
    run_dir.mkdir(parents=True, exist_ok=True)
    rows_path = run_dir / "rows.jsonl"

    manifest = load_manifest(manifest_path)
    if limit is not None:
        manifest = manifest[:limit]

    index = None
    if index_path is not None and Path(index_path).exists():
        from .proof_retrieval import load_index
        index = load_index(index_path)

    done_ids = _read_done_ids(rows_path)
    n_certified = len(done_ids)
    n_total = len(manifest)

    with rows_path.open("a") as fh:
        for entry in manifest:
            if entry["id"] in done_ids:
                continue
            rows = run_one_theorem(model, entry, lmgpa_root, index, run_dir,
                                    k_iters=k_iters, timeout=timeout, checker=checker)
            for row in rows:
                fh.write(json.dumps(row) + "\n")
            fh.flush()
            if rows and rows[-1]["certified"]:
                n_certified += 1
            print(f"[proof_gen] {entry['id']}: certified={rows[-1]['certified'] if rows else False} "
                  f"tally={n_certified}/{n_total}")

    return {"n_certified": n_certified, "n_total": n_total, "floor": f"{n_certified}/{n_total}"}


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv=None):
    parser = argparse.ArgumentParser(prog="python3 -m harness.proof_gen")
    sub = parser.add_subparsers(dest="cmd", required=True)

    run_p = sub.add_parser("run")
    run_p.add_argument("--manifest", default=str(MANIFEST_PATH))
    run_p.add_argument("--model", required=True, help="e.g. openai:<model-id>")
    run_p.add_argument("--run-id", required=True)
    run_p.add_argument("--limit", type=int, default=None)
    run_p.add_argument("--k-iters", type=int, default=DEFAULT_K_ITERS)
    run_p.add_argument("--index", default=str(DEFAULT_INDEX_PATH))
    run_p.add_argument("--lmgpa-root", default=str(DEFAULT_LMGPA_ROOT))
    run_p.add_argument("--timeout", type=int, default=300)

    args = parser.parse_args(argv)
    if args.cmd == "run":
        from .repair import make_model
        model = make_model(args.model)
        run_dir = Path("results/runs") / args.run_id
        result = run_proof_gen(model, manifest_path=Path(args.manifest), run_dir=run_dir,
                                k_iters=args.k_iters, limit=args.limit,
                                index_path=Path(args.index), lmgpa_root=Path(args.lmgpa_root),
                                timeout=args.timeout)
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
