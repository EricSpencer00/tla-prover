"""CPU-only bounded comparison of original and explicitly grouped references."""
import argparse
import hashlib
from importlib.metadata import version
import json
from pathlib import Path
import site
import statistics
import time

GRAMMAR_SHA = '2bcc86946f0a858628f455a3d0648c7117e2b780743e1f25dff82cebd0fb4d67'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--model', type=Path, required=True)
    parser.add_argument('--grammar', type=Path, required=True)
    parser.add_argument('--cases', type=Path, required=True)
    parser.add_argument('--xgrammar-site', type=Path, required=True)
    parser.add_argument('--changed-region', action='store_true',
                        help='Separate diagnostic: prime common prefix, time at most32 changed-region tokens')
    args = parser.parse_args()
    if sha(args.grammar) != GRAMMAR_SHA:
        raise ValueError('Grammar identity mismatch')
    cases = json.loads(args.cases.read_text())['cases']
    if [(c['row'], c['format']) for c in cases] != [
            (47, 'original'), (47, 'grouped'), (107, 'original'), (107, 'grouped')]:
        raise ValueError('Unexpected paired reference cases')
    if any(hashlib.sha256(c['text'].encode()).hexdigest() != c['text_sha256'] for c in cases):
        raise ValueError('Case digest mismatch')
    site.addsitedir(str(args.xgrammar_site))
    import xgrammar as xgr
    from transformers import AutoTokenizer
    if version('xgrammar') != '0.2.2':
        raise ValueError('Expected exact Polaris XGrammar0.2.2')
    tokenizer = AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    encoded = [tokenizer.encode(c['text'], add_special_tokens=False) for c in cases]
    common = {}
    for index in (0, 2):
        a, b = encoded[index:index+2]
        common[cases[index]['row']] = next((i for i, (x, y) in enumerate(zip(a, b)) if x != y), min(len(a), len(b)))
    vocab_size = json.loads((args.model / 'config.json').read_text())['vocab_size']
    info = xgr.TokenizerInfo.from_huggingface(tokenizer, vocab_size=vocab_size)
    started = time.monotonic()
    compiled = xgr.GrammarCompiler(info, max_threads=1).compile_grammar(args.grammar.read_text())
    print(json.dumps(dict(event='identity', grammar_sha256=GRAMMAR_SHA,
        cases_sha256=sha(args.cases), source_sha256=sha(__file__), xgrammar_version=version('xgrammar'),
        tokenizer_sha256=sha(args.model / 'tokenizer.json'), compile_seconds=time.monotonic()-started,
        changed_region=args.changed_region, common_prefix_tokens=common,
        scope='Four reference-prefix CPU diagnostics, no model weights or CUDA operations')), flush=True)
    for case, ids in zip(cases, encoded):
        begin = common[case['row']] if args.changed_region else 0
        if begin == len(ids):
            print(json.dumps(dict(event='case_skipped_identical_reference', row=case['row'],
                format=case['format'], text_sha256=case['text_sha256'], common_prefix_tokens=begin)), flush=True)
            continue
        planned = min(32 if args.changed_region else 128, len(ids)-begin)
        matcher = xgr.GrammarMatcher(compiled)
        if not all(matcher.accept_token(token) for token in ids[:begin]):
            raise ValueError('Grammar rejected primed reference prefix')
        mask = xgr.allocate_token_bitmask(1, vocab_size)
        durations, rejected = [], False
        started = time.monotonic()
        for index, token in enumerate(ids[begin:begin+planned], start=begin):
            if time.monotonic() - started >= 30:
                break
            step = time.monotonic()
            if not matcher.accept_token(token):
                rejected = True
                break
            matcher.fill_next_token_bitmask(mask)
            durations.append(time.monotonic()-step)
            print(json.dumps(dict(event='prefix', row=case['row'], format=case['format'],
                tokens=index+1, seconds=durations[-1])), flush=True)
        print(json.dumps(dict(event='case_complete', row=case['row'], format=case['format'],
            text_sha256=case['text_sha256'], full_reference_tokens=len(ids), planned_prefix_tokens=planned,
            primed_prefix_tokens=begin, priming_mask_cost_measured=False,
            measured_prefix_tokens=len(durations), all_planned_prefixes_measured=len(durations)==planned,
            token_rejected=rejected, elapsed_seconds=time.monotonic()-started,
            median_step_seconds=statistics.median(durations) if durations else None,
            max_step_seconds=max(durations, default=None),
            bound='30s per case checked between tokens; outer180s hard timeout',
            full_module_decode_claim=False, model_improvement_claim=False)), flush=True)
    print(json.dumps(dict(event='complete', cases=4, model_weights_loaded=False)), flush=True)


if __name__ == '__main__':
    main()
