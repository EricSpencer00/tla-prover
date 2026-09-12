"""Exact-runtime reference/EOS and continuation-prefix grammar replay; no model weights."""
import argparse
import hashlib
import importlib.metadata
import json
from pathlib import Path
import site

GRAMMAR_SHA = "1f4124cd20bdfdfd41ba406703bb2d123ebb26190fd3834cbb3df32dcb1cc000"
CORPUS_SHA = "fb76468f6a3217a359d54da92a2e3fa25396aad0547e6b5eb35129193a0e812a"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def split_reference(tokenizer, text):
    """Return a token-boundary prefix ending immediately before ``Next ==``."""
    encoded = tokenizer(text, add_special_tokens=False, return_offsets_mapping=True)
    ids, offsets = encoded["input_ids"], encoded["offset_mapping"]
    marker = text.index("Next ==")
    split = next(i for i, (start, _) in enumerate(offsets) if start >= marker)
    if offsets[split][0] != marker:
        raise ValueError("Next marker is not an exact tokenizer boundary")
    prefix_ids = ids[:split]
    prefix_text = text[:marker]
    # Llama's decoder does not promise byte-for-byte inversion of whitespace.
    # The operational invariant is stronger for continuation: re-encoding the
    # exact literal prefix must recover the exact prefix token IDs.
    reencoded = tokenizer(prefix_text, add_special_tokens=False)["input_ids"]
    if reencoded != prefix_ids:
        raise ValueError("exact prefix text does not re-encode to its frozen token IDs")
    return ids, prefix_ids, prefix_text, split


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--grammar", type=Path, required=True)
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--xgrammar-site", type=Path, required=True)
    args = parser.parse_args()
    if sha(args.grammar) != GRAMMAR_SHA or sha(args.corpus) != CORPUS_SHA:
        raise ValueError("frozen grammar/corpus hash mismatch")
    site.addsitedir(str(args.xgrammar_site))
    import xgrammar as xgr
    from transformers import AutoTokenizer
    if importlib.metadata.version("xgrammar") != "0.2.2":
        raise ValueError("exact xgrammar 0.2.2 required")
    tokenizer = AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    vocab = json.loads((args.model / "config.json").read_text())["vocab_size"]
    info = xgr.TokenizerInfo.from_huggingface(tokenizer, vocab_size=vocab)
    compiled = xgr.GrammarCompiler(info, max_threads=1).compile_grammar(args.grammar.read_text())
    refs = {r["row"]: r["text"] for r in json.loads(args.corpus.read_text())["references"]
            if r.get("row") in (47, 107)}
    if set(refs) != {47, 107}:
        raise ValueError("protected canonical references missing")
    eos = tokenizer.eos_token_id
    if not isinstance(eos, int):
        raise ValueError("single EOS token required")
    records = []
    for row in (47, 107):
        text = refs[row]
        ids, prefix_ids, prefix_text, split = split_reference(tokenizer, text)
        prefix_matcher = xgr.GrammarMatcher(compiled)
        if not all(prefix_matcher.accept_token(token) for token in prefix_ids):
            raise ValueError("canonical reference prefix rejected")
        if not prefix_matcher.accept_token(ids[split]):
            raise ValueError("first withheld reference token rejected")
        full_matcher = xgr.GrammarMatcher(compiled)
        if not all(full_matcher.accept_token(token) for token in ids):
            raise ValueError("complete canonical reference rejected")
        completed_before_eos = full_matcher.is_completed()
        eos_accepted = full_matcher.accept_token(eos)
        terminated_after_eos = full_matcher.is_terminated()
        if not completed_before_eos or not eos_accepted or not terminated_after_eos:
            raise ValueError("canonical reference completion/EOS contract failed")
        records.append(dict(row=row, reference_sha256=hashlib.sha256(text.encode()).hexdigest(),
            reference_tokens=len(ids), prefix_sha256=hashlib.sha256(prefix_text.encode()).hexdigest(),
            prefix_tokens=len(prefix_ids), withheld_tokens=len(ids)-len(prefix_ids),
            split_marker="Next ==", first_withheld_token_id=ids[split],
            completed_before_eos=completed_before_eos, eos_token_id=eos,
            eos_accepted=eos_accepted, terminated_after_eos=terminated_after_eos))
    print(json.dumps(dict(kind="protected_reference_eos_replay_v1", complete=True,
        grammar_sha256=GRAMMAR_SHA, corpus_sha256=CORPUS_SHA,
        tokenizer_sha256=sha(args.model / "tokenizer.json"), xgrammar_version="0.2.2",
        model_weights_loaded=False, records=records,
        scope="Reference/EOS and token-boundary preflight only; no model or gate credit",
        gate_claim=False, model_improvement_claim=False), sort_keys=True))


if __name__ == "__main__":
    main()
