"""Exact-runtime differential control for ranked greedy grammar selection.

No model weights. Reference prefixes are primed only as checker states; random,
tied and adversarial synthetic scores compare selection against full masks.
"""
import argparse
import hashlib
from importlib.metadata import version
import json
from pathlib import Path
import site
import time

GRAMMAR_SHA = '1f4124cd20bdfdfd41ba406703bb2d123ebb26190fd3834cbb3df32dcb1cc000'
CORPUS_SHA = 'fb76468f6a3217a359d54da92a2e3fa25396aad0547e6b5eb35129193a0e812a'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('grammar', 'corpus', 'model', 'xgrammar-site', 'output'):
        p.add_argument('--' + name, type=Path, required=True)
    args = p.parse_args()
    if (digest(args.grammar) != GRAMMAR_SHA or digest(args.corpus) != CORPUS_SHA
            or args.output.exists()):
        raise ValueError('Exact inputs and append-only output required')
    site.addsitedir(str(args.xgrammar_site))
    import xgrammar as xgr
    import torch
    from transformers import AutoTokenizer
    from protected_greedy_grammar_selector import GreedyGrammarSelector
    if version('xgrammar') != '0.2.2':
        raise ValueError('Exact0.2.2 required')
    tok = AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    vocab = json.loads((args.model / 'config.json').read_text())['vocab_size']
    grammar = args.grammar.read_text()
    compiler = xgr.GrammarCompiler(xgr.TokenizerInfo.from_huggingface(tok, vocab_size=vocab), max_threads=1)
    compiled = compiler.compile_grammar(grammar)
    corpus = json.loads(args.corpus.read_text())
    refs = sorted((r for r in corpus['references'] if r['row'] is not None), key=lambda r: r['row'])
    if [r['row'] for r in refs] != [47, 107]:
        raise ValueError('Protected cases missing')
    records = []
    for r in refs:
        all_ids = tok.encode(r['text'], add_special_tokens=False)
        for count in (0, 22, 64, 128):
            ids = all_ids[:count]
            dense = xgr.GrammarMatcher(compiled)
            if not all(dense.accept_token(t) for t in ids):
                raise ValueError('Primed prefix rejected')
            bitmask = xgr.allocate_token_bitmask(1, vocab)
            start = time.monotonic()
            dense.fill_next_token_bitmask(bitmask)
            dense_seconds = time.monotonic() - start
            token_ids = torch.arange(vocab)
            allowed = ((bitmask[0, token_ids // 32].to(torch.int64) >> (token_ids % 32)) & 1).bool()
            legal = torch.nonzero(allowed).flatten()
            illegal = torch.nonzero(~allowed).flatten()
            if not len(legal):
                raise ValueError('No legal token in control prefix')
            torch.manual_seed(20261011 + r['row'] + count)
            random_scores = torch.randn((1, vocab))
            adversarial = torch.full((1, vocab), -float('inf'))
            adversarial[0, illegal[:129]] = 2.0
            adversarial[0, legal[0]] = 1.0
            for label, scores in [('random', random_scores), ('ties', torch.zeros((1, vocab))),
                                  ('129_illegal_first', adversarial)]:
                reference = int(scores.masked_fill(~allowed.unsqueeze(0), -float('inf')).argmax())
                selector = GreedyGrammarSelector(xgr, compiled)
                if not all(selector.matcher.accept_token(t) for t in ids):
                    raise ValueError('Selector primed prefix rejected')
                before = time.monotonic()
                actual_scores = selector(torch.tensor([[0]]), scores)
                elapsed = time.monotonic() - before
                actual = int(actual_scores.argmax())
                selector.validate_generated([actual])
                if actual != reference or not bool(allowed[actual]):
                    raise ValueError('Ranked selection differs from dense mask')
                record = dict(row=r['row'], primed_tokens=count, scenario=label,
                    dense_seconds=dense_seconds, selector_seconds=elapsed,
                    candidates_checked=selector.candidates_checked, selected=actual,
                    reference=reference, equivalent=True)
                records.append(record)
                print(json.dumps(dict(event='case', **record)), flush=True)
    # Exact-runtime rejection rollback, multi-step prefix protocol and EOS.
    tiny = xgr.GrammarCompiler(xgr.TokenizerInfo(
        ['ax', 'a', 'b', 'ab', 'x', '<eos>'], stop_token_ids=[5]), max_threads=1).compile_grammar('root ::= "ab"')
    stop_probe = GreedyGrammarSelector(xgr, tiny, audit_steps=3)
    prompt = torch.tensor([[4, 4]])
    for expected in (1, 2, 5):
        selected = int(stop_probe(prompt, torch.tensor([[10., 9., 8., 7., 6., 11.]])).argmax())
        if selected != expected:
            raise ValueError('Exact-runtime rollback/EOS control failed')
        prompt = torch.cat([prompt, torch.tensor([[selected]])], dim=1)
    stop_probe.validate_generated([1, 2, 5])
    if not stop_probe.matcher.is_terminated() or stop_probe.audit_count != 3:
        raise ValueError('Exact-runtime termination or audit control failed')
    result = dict(complete=True, cases=records, all_equivalent=len(records)==24,
        eos_rollback_control=True, control_full_mask_audits=3,
        grammar_sha256=GRAMMAR_SHA, corpus_sha256=CORPUS_SHA,
        source_sha256=digest(Path(__file__)),
        selector_sha256=digest(Path(__file__).with_name('protected_greedy_grammar_selector.py')),
        tokenizer_sha256=digest(args.model / 'tokenizer.json'), xgrammar_version=version('xgrammar'),
        model_weights_loaded=False, gate_claim=False,
        scope='Synthetic logits at8 fixed reference states; not model throughput or quality',
        gpu_trial_supported=len(records)==24 and max(r['selector_seconds'] for r in records)<0.2)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(event='complete', all_equivalent=result['all_equivalent'],
                          gpu_trial_supported=result['gpu_trial_supported'])), flush=True)


if __name__ == '__main__':
    main()
