"""CPU timing control: separate token acceptance, mask fill, and grammar cost.

The ASCII grammar is deliberately permissive and is NEVER an inference or
quality candidate. Both arms consume identical reference prefixes, no model.
"""
import argparse
import hashlib
from importlib.metadata import version
import json
from pathlib import Path
import site
import socket
import time

GRAMMAR_SHA = '1f4124cd20bdfdfd41ba406703bb2d123ebb26190fd3834cbb3df32dcb1cc000'
CORPUS_SHA = 'fb76468f6a3217a359d54da92a2e3fa25396aad0547e6b5eb35129193a0e812a'
CONTROL = r'root ::= [\x00-\x7f]*'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('grammar', 'corpus', 'model', 'xgrammar-site'):
        p.add_argument('--' + name, type=Path, required=True)
    p.add_argument('--debug-prefix', type=int, choices=range(1, 129),
                   help='Inspect one mask per row after priming this many tokens; not a speed comparison')
    args = p.parse_args()
    if digest(args.grammar) != GRAMMAR_SHA or digest(args.corpus) != CORPUS_SHA:
        raise ValueError('Exact prior grammar/corpus required')
    site.addsitedir(str(args.xgrammar_site))
    import xgrammar as xgr
    import torch
    from transformers import AutoTokenizer
    if version('xgrammar') != '0.2.2':
        raise ValueError('Exact runtime required')
    tok = AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    vocab = json.loads((args.model / 'config.json').read_text())['vocab_size']
    compiler = xgr.GrammarCompiler(xgr.TokenizerInfo.from_huggingface(tok, vocab_size=vocab), max_threads=1)
    refs = sorted((r for r in json.loads(args.corpus.read_text())['references'] if r['row'] is not None),
                  key=lambda r: r['row'])
    if [r['row'] for r in refs] != [47, 107]:
        raise ValueError('Both protected timing cases required')
    records = []
    print(json.dumps(dict(event='runtime', host=socket.gethostname(), threads=torch.get_num_threads(),
        interop_threads=torch.get_num_interop_threads(), xgrammar=version('xgrammar'),
        source_sha256=digest(Path(__file__)), grammar_sha256=GRAMMAR_SHA, corpus_sha256=CORPUS_SHA,
        tokenizer_sha256=digest(args.model / 'tokenizer.json'))), flush=True)
    if args.debug_prefix is not None:
        compiled = compiler.compile_grammar(args.grammar.read_text())
        print(json.dumps(dict(event='compiled_grammar', memory_size_bytes=compiled.memory_size_bytes,
                              grammar=str(compiled.grammar))), flush=True)
        for r in refs:
            ids = tok.encode(r['text'], add_special_tokens=False)[:args.debug_prefix]
            matcher = xgr.GrammarMatcher(compiled)
            if not all(matcher.accept_token(token) for token in ids):
                raise ValueError('Debug prefix rejected')
            print(json.dumps(dict(event='debug_prefix', row=r['row'], tokens=len(ids),
                                  pieces=[tok.decode([token]) for token in ids])), flush=True)
            mask = xgr.allocate_token_bitmask(1, vocab)
            matcher.fill_next_token_bitmask(mask, debug_print=True)
        print(json.dumps(dict(event='debug_complete', model_weights_loaded=False, quality_claim=False)), flush=True)
        return
    for label, grammar in [('ascii_timing_control', CONTROL), ('canonical', args.grammar.read_text())]:
        compiled = compiler.compile_grammar(grammar)
        for r in refs:
            ids = tok.encode(r['text'], add_special_tokens=False)[:32]
            matcher = xgr.GrammarMatcher(compiled)
            mask = xgr.allocate_token_bitmask(1, vocab)
            steps = []
            start = time.monotonic()
            for index, token in enumerate(ids):
                if time.monotonic() - start >= 20:
                    break
                before = time.monotonic()
                accepted = matcher.accept_token(token)
                middle = time.monotonic()
                if not accepted:
                    raise ValueError('Timing prefix rejected')
                matcher.fill_next_token_bitmask(mask)
                after = time.monotonic()
                steps.append(dict(index=index, accept_seconds=middle-before, fill_seconds=after-middle))
            record = dict(arm=label, row=r['row'], planned=len(ids), measured=len(steps),
                          elapsed_seconds=time.monotonic()-start, steps=steps)
            records.append(record)
            print(json.dumps(dict(event='case', **record)), flush=True)
    print(json.dumps(dict(event='complete', cases=len(records), model_weights_loaded=False,
        quality_claim=False, warning='ASCII control is not a candidate grammar; fixed control-first timing order')),
        flush=True)


if __name__ == '__main__':
    main()
