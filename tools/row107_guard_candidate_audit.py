"""Audit grammar/guard candidates at the frozen row-107 repair boundary.

Run this on the pinned Polaris runtime.  It loads only the tokenizer and
XGrammar grammar; it never loads model weights or touches CUDA.  The result
distinguishes an already-invalid accepted prefix from a genuine no-token
continuation and makes no SANY or quality claim.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import site
import sys


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--row", type=Path, required=True)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--grammar", type=Path, required=True)
    parser.add_argument("--xgrammar-site", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    if str(Path.cwd()) not in sys.path:
        sys.path.insert(0, str(Path.cwd()))
    site.addsitedir(str(args.xgrammar_site))
    from transformers import AutoTokenizer
    import torch
    import xgrammar
    from layout_junction_audit import line_guard
    from precedence_guard import precedence_guard

    row = json.loads(args.row.read_text())
    tokenizer = AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    response_ids = tokenizer.encode(row["baseline_reply"], add_special_tokens=False)
    prefix_ids = response_ids[:row["accepted_prefix_tokens"]]
    prefix = tokenizer.decode(prefix_ids, skip_special_tokens=False,
                             clean_up_tokenization_spaces=False)
    info = xgrammar.TokenizerInfo.from_huggingface(tokenizer, vocab_size=128256)
    compiled = xgrammar.GrammarCompiler(info, max_threads=1).compile_grammar(
        args.grammar.read_text())
    matcher = xgrammar.GrammarMatcher(compiled)
    accepted = 0
    for token in prefix_ids:
        if not matcher.accept_token(int(token)):
            break
        accepted += 1

    bitmask = xgrammar.allocate_token_bitmask(1, 128256).cpu()
    matcher.fill_next_token_bitmask(bitmask)
    words = bitmask[0].to(dtype=torch.int64)
    shifts = torch.arange(32, dtype=torch.int64)
    allowed = ((words[:, None] >> shifts) & 1).bool().flatten()[:128256]
    counts = {"grammar_allowed": 0, "layout_reject": 0,
              "precedence_reject": 0, "both_reject": 0,
              "guard_allowed": 0}
    examples = {"layout": [], "precedence": [], "both": [], "allowed": []}
    for token in allowed.nonzero().flatten().tolist():
        counts["grammar_allowed"] += 1
        piece = tokenizer.decode([int(token)], skip_special_tokens=False,
                                 clean_up_tokenization_spaces=False)
        layout_hit = bool(line_guard(prefix + piece))
        precedence_hit = bool(precedence_guard(prefix + piece))
        if layout_hit:
            counts["layout_reject"] += 1
        if precedence_hit:
            counts["precedence_reject"] += 1
        if layout_hit and precedence_hit:
            counts["both_reject"] += 1
        label = ("both" if layout_hit and precedence_hit else
                 "layout" if layout_hit else
                 "precedence" if precedence_hit else "allowed")
        if label == "allowed":
            counts["guard_allowed"] += 1
        if len(examples[label]) < 12:
            examples[label].append({"token": int(token), "piece": piece})

    result = {
        "kind": "row107_guard_candidate_audit_v1",
        "row": row["row"],
        "baseline_tokens": len(response_ids),
        "requested_prefix_tokens": row["accepted_prefix_tokens"],
        "accepted_prefix_replay": accepted,
        "prefix_layout_hits": line_guard(prefix),
        "prefix_precedence_hits": precedence_guard(prefix),
        "counts": counts,
        "examples": examples,
        "inputs": {"row_sha256": __import__("hashlib").sha256(
            args.row.read_bytes()).hexdigest()},
        "claims": {"model_weights_loaded": False, "cuda_touched": False,
                   "sany_claim": False, "model_improvement_claim": False,
                   "gate_claim": False},
    }
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({k: result[k] for k in
                      ("kind", "row", "accepted_prefix_replay", "prefix_precedence_hits", "counts", "claims")},
                     ensure_ascii=False, sort_keys=True))


if __name__ == "__main__":
    main()
