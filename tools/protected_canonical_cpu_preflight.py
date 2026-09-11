"""Exact-runtime canonical syntax coverage and bounded CPU mask preflight."""
import argparse
import hashlib
from importlib.metadata import version
import json
from pathlib import Path
import re
import site
import time

GRAMMAR_SHA = '1f4124cd20bdfdfd41ba406703bb2d123ebb26190fd3834cbb3df32dcb1cc000'
PACKET_SHA = 'a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c'
PROTECTED = {'w4-fullmodule:w4opus::d2-m7-p4-t2': 47, 'w4-fullmodule:w4opus::d3-m0-p0-t0': 107}


def sha(value):
    return hashlib.sha256(value).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def prepare(args):
    if sha(args.packet.read_bytes()) != PACKET_SHA or args.output.exists():
        raise ValueError('Packet identity or append-only output mismatch')
    rows = [r for r in json.loads(args.packet.read_bytes())['rows'] if r['response'].startswith('---- MODULE')]
    receipts = json.loads((args.roundtrip / 'rows.json').read_text())
    if len(rows) != 84 or len(receipts) != 84:
        raise ValueError('All84 references required')
    refs = []
    for index, (r, v) in enumerate(zip(rows, receipts)):
        name = re.match(r'-{4,} MODULE (\w+) -{4,}', r['response']).group(1)
        text = (args.roundtrip / 'references' / str(index) / (name + '.tla')).read_text()
        if (v['id'] != r['id'] or v['original_sha256'] != r['response_sha256']
                or not v['same_structure'] or v['status'] != 'pass' or sha(text.encode()) != v['source_sha256']):
            raise ValueError('Invalid structural reference provenance')
        refs.append(dict(id=r['id'], row=PROTECTED.get(r['id']), text=text, sha256=sha(text.encode())))
    bad = []
    for path in sorted(args.records.glob('row-*.json')):
        r = json.loads(path.read_text())
        if sha(r['raw_reply'].encode()) != r['raw_reply_sha256']:
            raise ValueError('Failure source digest mismatch')
        bad.append(dict(id=path.name, text=r['raw_reply'], sha256=r['raw_reply_sha256']))
    if len(bad) != 6:
        raise ValueError('Six saved failure records required; missing model outputs are not part of this control set')
    dump(args.output, dict(packet_sha256=PACKET_SHA, references=refs, saved_failures=bad,
                          scope='Checker controls only; never generation input', model_improvement_claim=False))


def check(args):
    if sha(args.grammar.read_bytes()) != GRAMMAR_SHA or args.output.exists():
        raise ValueError('Grammar identity or append-only output mismatch')
    corpus = json.loads(args.corpus.read_text())
    refs, bad = corpus['references'], corpus['saved_failures']
    if corpus['packet_sha256'] != PACKET_SHA or len(refs) != 84 or len(bad) != 6:
        raise ValueError('Unexpected coverage corpus')
    if any(sha(r['text'].encode()) != r['sha256'] for r in refs + bad):
        raise ValueError('Corpus text digest mismatch')
    print(json.dumps(dict(event='import_start')), flush=True)
    site.addsitedir(str(args.xgrammar_site))
    import xgrammar as xgr
    from transformers import AutoTokenizer
    print(json.dumps(dict(event='imports_complete', xgrammar_version=version('xgrammar'))), flush=True)
    if version('xgrammar') != '0.2.2':
        raise ValueError('Expected exact XGrammar0.2.2')
    grammar = xgr.Grammar.from_ebnf(args.grammar.read_text())
    compiled_chars = xgr.GrammarCompiler(xgr.TokenizerInfo([], vocab_size=0), max_threads=1).compile_grammar(grammar)
    print(json.dumps(dict(event='character_grammar_compiled')), flush=True)

    def accepts(text):
        matcher = xgr.GrammarMatcher(compiled_chars)
        return matcher.accept_string(text) and matcher.is_completed()

    coverage = [dict(id=r['id'], accepted=accepts(r['text'])) for r in refs]
    failures = [dict(id=r['id'], accepted=accepts(r['text'])) for r in bad]
    print(json.dumps(dict(event='coverage', accepted=sum(r['accepted'] for r in coverage),
                          rejected_failures=sum(not r['accepted'] for r in failures))), flush=True)
    tokenizer = AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    print(json.dumps(dict(event='tokenizer_loaded')), flush=True)
    vocab_size = json.loads((args.model / 'config.json').read_text())['vocab_size']
    info = xgr.TokenizerInfo.from_huggingface(tokenizer, vocab_size=vocab_size)
    started = time.monotonic()
    compiled = xgr.GrammarCompiler(info, max_threads=1).compile_grammar(grammar)
    compilation = time.monotonic() - started
    print(json.dumps(dict(event='token_grammar_compiled', seconds=compilation)), flush=True)
    masks = []
    selected = sorted((r for r in refs if r['row'] is not None), key=lambda r: r['row'])
    if [r['row'] for r in selected] != [47, 107]:
        raise ValueError('Protected prefix controls missing')
    for r in selected:
        ids = tokenizer.encode(r['text'], add_special_tokens=False)
        matcher = xgr.GrammarMatcher(compiled)
        mask = xgr.allocate_token_bitmask(1, vocab_size)
        times, rejected = [], False
        started = time.monotonic()
        for index, token in enumerate(ids[:128]):
            if time.monotonic() - started >= 30:
                break
            step = time.monotonic()
            if not matcher.accept_token(token):
                rejected = True
                break
            matcher.fill_next_token_bitmask(mask)
            times.append(time.monotonic() - step)
        masks.append(dict(row=r['row'], planned=min(128, len(ids)), measured=len(times),
                          rejected=rejected, elapsed_seconds=time.monotonic()-started,
                          max_step_seconds=max(times, default=0), step_seconds=times))
        print(json.dumps(dict(event='mask_case', **{k: v for k, v in masks[-1].items() if k != 'step_seconds'})), flush=True)
    summary = dict(grammar_sha256=GRAMMAR_SHA, corpus_sha256=sha(args.corpus.read_bytes()),
        source_sha256=sha(Path(__file__).read_bytes()), xgrammar_version=version('xgrammar'),
        tokenizer_sha256=sha((args.model / 'tokenizer.json').read_bytes()),
        coverage=coverage, failures=failures, masks=masks, compile_seconds=compilation,
        bounded_gpu_preflight_pass=all(r['accepted'] for r in coverage) and
            all(not r['accepted'] for r in failures) and
            all(m['measured'] == m['planned'] and not m['rejected'] and m['elapsed_seconds'] <= 12.8 for m in masks),
        readiness_rule='All84 equivalent forms, six failure controls, full128-token prefixes each within12.8s; not a generation guarantee',
        model_weights_loaded=False, cuda_touched=False, gate_claim=False, model_improvement_claim=False,
        raw_spelling_coverage='Canonical-only:80/84 original list spellings excluded; equivalents verified separately')
    dump(args.output, summary)
    print(json.dumps(dict(event='complete', bounded_gpu_preflight_pass=summary['bounded_gpu_preflight_pass'])), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='mode', required=True)
    p = sub.add_parser('prepare')
    for name in ('packet', 'roundtrip', 'records', 'output'):
        p.add_argument('--' + name, type=Path, required=True)
    p = sub.add_parser('check')
    for name in ('model', 'grammar', 'corpus', 'xgrammar-site', 'output'):
        p.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    (prepare if args.mode == 'prepare' else check)(args)


if __name__ == '__main__':
    try:
        main()
    except BaseException as exc:
        # Preserve failures even if a dependency changes Python's stderr.
        if not (isinstance(exc, SystemExit) and exc.code in (None, 0)):
            print(json.dumps(dict(event='exception', type=type(exc).__name__, message=str(exc))), flush=True)
        raise
