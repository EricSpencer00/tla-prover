"""Verify that v6 prefix extraction stops before the precedence violation."""
from __future__ import annotations

import argparse
import hashlib
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
    info = xgrammar.TokenizerInfo.from_huggingface(tokenizer, vocab_size=128256)
    compiled = xgrammar.GrammarCompiler(info, max_threads=1).compile_grammar(
        args.grammar.read_text())
    matcher = xgrammar.GrammarMatcher(compiled)
    accepted = []
    response_text = ""
    stop = None
    for index, token in enumerate(response_ids):
        piece = tokenizer.decode([int(token)], skip_special_tokens=False,
                                 clean_up_tokenization_spaces=False)
        candidate = response_text + piece
        if line_guard(candidate) or precedence_guard(candidate):
            stop = {"index": index, "token": int(token),
                    "layout_hits": line_guard(candidate),
                    "precedence_hits": precedence_guard(candidate)}
            break
        if not matcher.accept_token(int(token)):
            stop = {"index": index, "token": int(token),
                    "reason": "grammar_reject"}
            break
        accepted.append(int(token))
        response_text = candidate

    bitmask = xgrammar.allocate_token_bitmask(1, 128256).cpu()
    matcher.fill_next_token_bitmask(bitmask)
    words = bitmask[0].to(dtype=torch.int64)
    shifts = torch.arange(32, dtype=torch.int64)
    allowed = ((words[:, None] >> shifts) & 1).bool().flatten()[:128256]
    guard_allowed = 0
    examples = []
    for token in allowed.nonzero().flatten().tolist():
        piece = tokenizer.decode([int(token)], skip_special_tokens=False,
                                 clean_up_tokenization_spaces=False)
        if not line_guard(response_text + piece) and not precedence_guard(response_text + piece):
            guard_allowed += 1
            if len(examples) < 12:
                examples.append({"token": int(token), "piece": piece})
    result = {
        "kind": "row107_prefix_admission_audit_v1",
        "row": row["row"],
        "requested_prefix_tokens": row["accepted_prefix_tokens"],
        "admitted_prefix_tokens": len(accepted),
        "stop": stop,
        "grammar_allowed_next_tokens": int(allowed.sum().item()),
        "guard_allowed_next_tokens": guard_allowed,
        "guard_allowed_examples": examples,
        "row_sha256": hashlib.sha256(args.row.read_bytes()).hexdigest(),
        "claims": {"model_weights_loaded": False, "cuda_touched": False,
                   "sany_claim": False, "model_improvement_claim": False,
                   "gate_claim": False},
    }
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({k: result[k] for k in
                      ("kind", "admitted_prefix_tokens", "stop",
                       "grammar_allowed_next_tokens", "guard_allowed_next_tokens",
                       "claims")}, ensure_ascii=False, sort_keys=True))
    if result["admitted_prefix_tokens"] >= row["accepted_prefix_tokens"]:
        raise SystemExit("prefix admission did not stop before the known bad boundary")
    if result["guard_allowed_next_tokens"] <= 0:
        raise SystemExit("prefix admission left no guard-allowed continuation")


if __name__ == "__main__":
    main()
