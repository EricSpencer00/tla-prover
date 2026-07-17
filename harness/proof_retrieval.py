"""W3.3: retrieval over verified proofs (PLAN.md W3.3).

Fine-tuning is shelved (Amendment 17); the prompt-only proof loop needs a
pure retrieval/heuristic premise-selection step in front of the SMT backend
instead. This module builds a flat index of every PROVED obligation row
harvested by harness/proof_traces.py (corpus-v1 + examples-v1, ~13.7k
obligations total, ~5,047 proved) and answers similarity queries over it.

Method (deliberately dependency-free, no embeddings/GPU):
- Index build: filter rows.jsonl to status == "proved", normalize each
  obligation_text with harness.corpora.normalize_tla (comment-stripped,
  whitespace-insensitive token list -- same normalizer used by the W2.1
  dedup/decontamination funnel, reused here for consistency), and record the
  backend that discharged it, the source module, and (best-effort) the BY/USE
  facts immediately following the obligation's location in the original
  module text.
- Query: normalize the query obligation text the same way, then rank index
  entries by k-shingle (k=5, harness.corpora.SHINGLE_K) Jaccard similarity
  against the stored normalized token stream. Ties broken by insertion order
  (stable sort). This is the same shingle/Jaccard primitive already used and
  tested for near-dup decontamination in corpora.py -- reusing it here avoids
  a second, subtly-different similarity metric in the repo.

BY/USE recovery is best-effort only: it scans the original module file (not
the traced copy in a tlapm scratch dir, which no longer exists) for BY/USE
lines starting within a few lines after the obligation's end location. If the
module file is missing (e.g. moved since the trace was harvested) or no BY/
USE line is found nearby, by_facts is an empty list -- callers must treat it
as optional context, never as a required field.
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from .corpora import jaccard, normalize_tla, shingle_set

_LOC_RE = re.compile(r"^(\d+):\d+:(\d+):\d+")
_BY_USE_RE = re.compile(r"^(BY|USE)\b")

BY_FACTS_LOOKAHEAD = 6


def _by_facts_near(module_path: str | None, loc: str | None, lookahead: int = BY_FACTS_LOOKAHEAD) -> list[str]:
    """Best-effort BY/USE line(s) immediately following an obligation's end
    line in its source module text. Empty list if module_path is missing,
    unreadable, loc is unparseable, or no BY/USE line appears within
    `lookahead` lines of the obligation's end line."""
    if not module_path or not loc:
        return []
    m = _LOC_RE.match(loc)
    if not m:
        return []
    end_line = int(m.group(2))
    p = Path(module_path)
    try:
        text = p.read_text(errors="replace")
    except OSError:
        return []
    lines = text.split("\n")
    facts = []
    # end_line is 1-indexed and points at (or before) the last line of the
    # obligation; scan forward from there.
    for i in range(end_line, min(end_line + lookahead, len(lines))):
        stripped = lines[i].strip()
        if _BY_USE_RE.match(stripped):
            facts.append(stripped)
        elif facts:
            break
    return facts


def build_index(trace_dirs, out_path) -> list[dict]:
    """Read rows.jsonl from each dir in `trace_dirs`, keep only proved
    obligations, and write one JSON object per line to `out_path` (JSONL,
    regardless of the out_path extension). Returns the list of entries
    written (for callers/tests that want counts without re-reading disk)."""
    entries = []
    for d in trace_dirs:
        rows_path = Path(d) / "rows.jsonl"
        if not rows_path.exists():
            continue
        with open(rows_path) as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                row = json.loads(line)
                if row.get("status") != "proved":
                    continue
                tokens = normalize_tla(row.get("obligation_text", "") or "")
                if not tokens:
                    continue
                entries.append({
                    "id": f"{row.get('module_id')}#{row.get('obligation_id')}",
                    "goal_text_normalized": " ".join(tokens),
                    "backend": row.get("backend"),
                    "module": row.get("module"),
                    "module_path": row.get("module_path"),
                    "theorem_kind": row.get("theorem_kind"),
                    "theorem_name": row.get("theorem_name"),
                    "loc": row.get("loc"),
                    "by_facts": _by_facts_near(row.get("module_path"), row.get("loc")),
                    "source": row.get("source"),
                })

    out_path = Path(out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as fh:
        for e in entries:
            fh.write(json.dumps(e) + "\n")
    return entries


def load_index(index_path) -> list[dict]:
    """Load a JSONL index file written by build_index into a list of dicts."""
    entries = []
    with open(index_path) as fh:
        for line in fh:
            line = line.strip()
            if line:
                entries.append(json.loads(line))
    return entries


def query(index, obligation_text: str, k: int = 5) -> list[dict]:
    """Rank index entries by shingle-Jaccard similarity to `obligation_text`.

    `index` may be a path to a JSONL index file (loaded via load_index) or an
    already-loaded list of entry dicts. Returns up to `k` entries (highest
    score first), each augmented with a "score" field; zero-similarity
    entries are excluded. Empty index or no overlap at all -> []."""
    if isinstance(index, (str, Path)):
        index = load_index(index)

    q_tokens = normalize_tla(obligation_text or "")
    q_shingles = shingle_set(q_tokens)
    if not q_shingles or not index:
        return []

    scored = []
    for e in index:
        e_tokens = e.get("goal_text_normalized", "").split(" ") if e.get("goal_text_normalized") else []
        e_shingles = shingle_set([t for t in e_tokens if t])
        score = jaccard(q_shingles, e_shingles)
        if score > 0:
            scored.append((score, e))

    scored.sort(key=lambda pair: pair[0], reverse=True)
    results = []
    for score, e in scored[:k]:
        r = dict(e)
        r["score"] = score
        results.append(r)
    return results


def _cli(argv=None):
    ap = argparse.ArgumentParser(prog="python3 -m harness.proof_retrieval")
    sub = ap.add_subparsers(dest="cmd", required=True)

    b = sub.add_parser("build", help="build a retrieval index from proof-trace rows.jsonl dirs")
    b.add_argument("trace_dirs", nargs="+", help="dirs each containing a rows.jsonl (e.g. results/proof_traces/corpus-v1)")
    b.add_argument("--out", required=True, help="output JSONL index path")

    q = sub.add_parser("query", help="query an existing index for similar proved obligations")
    q.add_argument("--index", required=True, help="path to a JSONL index file")
    q.add_argument("--text", required=True, help="obligation text to query")
    q.add_argument("--k", type=int, default=5)

    args = ap.parse_args(argv)
    if args.cmd == "build":
        entries = build_index(args.trace_dirs, args.out)
        backends = {}
        for e in entries:
            backends[e.get("backend")] = backends.get(e.get("backend"), 0) + 1
        print(f"built {len(entries)} entries -> {args.out}")
        print(f"backend distribution: {backends}")
    elif args.cmd == "query":
        results = query(args.index, args.text, k=args.k)
        print(json.dumps(results, indent=2))


if __name__ == "__main__":
    _cli()
