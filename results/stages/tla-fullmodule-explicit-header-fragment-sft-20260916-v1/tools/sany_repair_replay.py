"""Bounded offline lint experiment; never edits source evaluation evidence."""
import argparse
import hashlib
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from harness.gen_eval import REPO, _score
from harness.runner import build_module_index
from tools.lint_repair_probe import lint


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--run', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--limit', type=int, default=8)
    args = ap.parse_args()
    args.run = args.run.resolve()
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output / 'logs').mkdir()
    corpus = Path(json.loads((args.run / 'config.json').read_text())['corpus'])
    index, paths = build_module_index(corpus)
    cfgs = [('override', REPO / 'corpus/configs/overrides'),
            ('original', corpus / 'cfg'), ('draft', REPO / 'corpus/configs/drafts')]
    selected, seen = [], set()
    for line in (args.run / 'rows.jsonl').read_text().splitlines():
        row = json.loads(line)
        if row.get('sany') != 'fail' or row['spec'] in seen:
            continue
        candidate = args.run / row['candidate_path']
        source = candidate.read_text()
        if hashlib.sha256(source.encode()).hexdigest() != row['candidate_sha256']:
            continue
        repaired, rules = lint(source)
        if not rules:
            continue
        selected.append((row, source, repaired, rules))
        seen.add(row['spec'])
        if len(selected) >= args.limit:
            break
    results = []
    for old, source, repaired, rules in selected:
        record = {'spec': old['spec'], 'source_sample': old['sample'],
                  'source_sha256': old['candidate_sha256'], 'rules': rules}
        for tag, text in [('before', source), ('after', repaired)]:
            (args.output / f"{old['spec']}-{tag}.tla").write_text(text)
            scored, verdict, _ = _score(
                old['spec'], text, corpus, index, paths, cfgs,
                args.output / 'work', args.output / 'logs', 15,
                log_name=f"{old['spec']}-{tag}.log")
            record[tag] = {'verdict': verdict, 'sany': scored.get('sany'),
                           'tlc': scored.get('tlc'),
                           'tlc_vacuity': scored.get('tlc_vacuity')}
        results.append(record)
        print(json.dumps(record), flush=True)
    summary = {'diagnostic_only': True, 'source_run': str(args.run),
               'selection': 'first lint-touched SANY failure per spec; not unbiased',
               'tlc_timeout_s': 15, 'results': results,
               'sany_recoveries': sum(r['before']['sany'] != 'pass' and
                                      r['after']['sany'] == 'pass' for r in results),
               'verified_passes_after': sum(r['after']['verdict'] == 'pass' for r in results)}
    (args.output / 'report.json').write_text(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
