"""Bounded CPU replay of saved token prefixes; never loads model weights."""
import argparse
import json
from pathlib import Path
import site
import time


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--model', type=Path, required=True)
    p.add_argument('--grammar', type=Path, required=True)
    p.add_argument('--record', type=Path, required=True)
    p.add_argument('--xgrammar-site', type=Path, required=True)
    args = p.parse_args()
    site.addsitedir(str(args.xgrammar_site))
    import xgrammar as xgr
    from transformers import AutoTokenizer
    started = time.monotonic()
    tokenizer = AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    vocab_size = json.loads((args.model / 'config.json').read_text())['vocab_size']
    info = xgr.TokenizerInfo.from_huggingface(tokenizer, vocab_size=vocab_size)
    compiler = xgr.GrammarCompiler(info, max_threads=1)
    compiled = compiler.compile_grammar(args.grammar.read_text())
    print(json.dumps(dict(event='compiled', seconds=time.monotonic()-started)), flush=True)
    record = json.loads(args.record.read_bytes())
    ids = tokenizer.encode(record['raw_reply'], add_special_tokens=False)
    matcher = xgr.GrammarMatcher(compiled)
    mask = xgr.allocate_token_bitmask(1, vocab_size)
    timings = []
    for index, token in enumerate(ids[:256]):
        start = time.monotonic()
        accepted = matcher.accept_token(token)
        if not accepted:
            print(json.dumps(dict(event='token_rejected', index=index, token=token)), flush=True)
            break
        matcher.fill_next_token_bitmask(mask)
        elapsed = time.monotonic()-start
        timings.append(elapsed)
        if index % 16 == 0 or elapsed > 1:
            print(json.dumps(dict(event='prefix', tokens=index+1, seconds=elapsed,
                                  total_seconds=time.monotonic()-started)), flush=True)
    print(json.dumps(dict(event='complete', checked=len(timings), max_step_seconds=max(timings, default=0),
                          total_seconds=time.monotonic()-started, cuda_touched=False)), flush=True)


if __name__ == '__main__':
    main()
