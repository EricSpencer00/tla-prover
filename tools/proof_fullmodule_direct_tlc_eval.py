"""Protected TLC/non-vacuity gate for a completed direct-vLLM receipt."""
import argparse, json, time
from pathlib import Path
from harness import runner

ROWS = (47, 107)

def main(a):
    src = json.loads(a.receipt.read_bytes())
    if src.get('complete') is not True or src.get('eval_rows') != list(ROWS):
        raise ValueError('complete two-row SANY receipt required')
    out = a.output.resolve()
    if out.exists():
        raise ValueError('append-only output already exists')
    out.mkdir(parents=True)
    records = {}
    started = time.monotonic()
    for i in ROWS:
        item = src['results'][str(i)]
        sany = item.get('sany', {})
        if not isinstance(sany, dict) or sany.get('sany') != 1 or not sany.get('module'):
            raise ValueError(f'row {i} lacks a SANY-passing extracted module')
        module = sany['module']
        name = runner.module_name(module)
        work = out / str(i); work.mkdir()
        (work / f'{name}.tla').write_text(module)
        cfg = (a.sany_output / 'reference' / str(i) / 'configuration.cfg').read_text()
        (work / f'{name}.cfg').write_text(cfg)
        status, vac, log, seconds = runner.check_tlc(mod=name, cfg_text=cfg,
            workdir=work, timeout=a.timeout)
        (work / 'tlc.log').write_text(log)
        records[str(i)] = {'module': name, 'tlc': status, 'vacuity': vac,
                           'seconds': seconds, 'nonvacuous': status == 'pass' and not vac}
    receipt = {'schema': 1, 'kind': 'protected_direct_tlc_nonvacuity_eval',
               'complete': True, 'source_sany_receipt': str(a.receipt),
               'eval_rows': list(ROWS), 'results': records,
               'elapsed_seconds': time.monotonic() - started,
               'tlc_claim': all(x['tlc'] == 'pass' for x in records.values()),
               'nonvacuity_claim': all(x['nonvacuous'] for x in records.values())}
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt))

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--receipt', type=Path, required=True)
    p.add_argument('--sany-output', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--timeout', type=int, default=120)
    main(p.parse_args())
