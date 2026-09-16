import argparse
import json
from pathlib import Path

import pytest

from tools import proof_broader_owned_verify as owned


@pytest.fixture
def setup(tmp_path, monkeypatch):
    args = argparse.Namespace(prompts=tmp_path/'prompts', generations=tmp_path/'gens',
        tokenizer_path=tmp_path/'tokenizer', output=tmp_path/'out')
    expected = [(str(i), 'train' if i < 32 else 'development') for i in range(36)]
    monkeypatch.setattr(owned, 'identity', lambda a: {'fixed': True})
    monkeypatch.setattr(owned.broader, 'export_tasks', lambda: ({}, [dict(id=i, split=s) for i,s in expected]))
    calls = []
    def execute(cmd, cwd, timeout):
        calls.append((cmd, cwd, timeout))
        return dict(command=list(cmd), cwd=str(cwd), returncode=0,
            output='All 1 obligations proved.\n', seconds=.1, timed_out=False,
            execution_complete=True, cleanup_complete=True, output_complete=True)
    monkeypatch.setattr(owned, 'run_owned', execute)
    def underlying(a):
        rows=[]
        for i, (task, split) in enumerate(expected):
            row=dict(id=task, split=split, certified=False, status='no_proof_fragment')
            if i < 2:
                work = a.output/'checks'/task/'proof-unique'
                work.mkdir(parents=True)
                cmd=['tlapm', '--strict', '--nofp', 'M.tla']
                rc, text, seconds, timeout = owned.runner.run_cmd(cmd, work, 30)
                result=dict(command=cmd, workdir=str(work), returncode=rc, output=text,
                    seconds=seconds, timed_out=timeout, certified=rc == 0 and not timeout,
                    status='pass' if rc == 0 and not timeout else 'timeout')
                owned.write(work/'result.json', result)
                (work/'tlapm.log').write_text(text)
                row.update(result)
            rows.append(row)
        (a.output/'rows.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
        owned.write(a.output/'summary.json', dict(verification_complete=True, requested_tasks=36))
    monkeypatch.setattr(owned.broader, 'verify', underlying)
    return args, calls, underlying


def test_scoped_restore_and_separate_records(setup):
    args,calls,_=setup
    original=owned.runner.run_cmd
    owned.verify(args)
    assert owned.runner.run_cmd is original
    assert len(calls)==2 and all(c[2]==30 for c in calls)
    admission=json.loads((args.output/'owned_admission.json').read_text())
    assert admission['admitted'] and admission['checked_tasks']==2
    assert len(admission['process_sha256'])==2
    config=json.loads((args.output/'owned_config.json').read_text())
    assert config['cleanup_reserve_seconds']==.5
    assert 'inherited runtime identity' in config['scope']


def test_exception_restores(setup, monkeypatch):
    args,_,_=setup
    original=owned.runner.run_cmd
    def fail(a): raise RuntimeError('interrupted')
    monkeypatch.setattr(owned.broader,'verify',fail)
    with pytest.raises(RuntimeError,match='interrupted'): owned.verify(args)
    assert owned.runner.run_cmd is original
    assert not json.loads((args.output/'owned_failure.json').read_text())['admitted']


def test_identity_drift_refuses_admission(setup,monkeypatch):
    args,_,underlying=setup
    def drift(a):
        underlying(a)
        monkeypatch.setattr(owned,'identity',lambda a: {'changed': True})
    monkeypatch.setattr(owned.broader,'verify',drift)
    with pytest.raises(RuntimeError,match='identity drift'): owned.verify(args)
    assert not (args.output/'owned_admission.json').exists()


@pytest.mark.parametrize('field',['execution_complete','cleanup_complete','output_complete'])
def test_incomplete_is_not_certified(setup,monkeypatch,field):
    args,_,_=setup
    execute=owned.run_owned
    def incomplete(*a):
        result=execute(*a);result[field]=False
        return result
    monkeypatch.setattr(owned,'run_owned',incomplete)
    owned.verify(args)
    rows=[json.loads(s) for s in (args.output/'rows.jsonl').read_text().splitlines()]
    assert not any(r['certified'] for r in rows)
    assert rows[0]['returncode']==-1 and rows[0]['timed_out']


@pytest.mark.parametrize('tamper',['output','certified','missing_record','population','log'])
def test_audit_rejects_tampering(setup,monkeypatch,tamper):
    args,_,underlying=setup
    def corrupt(a):
        underlying(a)
        path=a.output/'rows.jsonl'
        rows=[json.loads(s) for s in path.read_text().splitlines()]
        if tamper=='output': rows[0]['output']='different'
        elif tamper=='certified': rows[2]['certified']=True
        elif tamper=='population': rows.pop()
        elif tamper=='missing_record': (Path(rows[0]['workdir'])/'process.json').unlink()
        elif tamper=='log': (Path(rows[0]['workdir'])/'tlapm.log').write_text('changed')
        path.write_text(''.join(json.dumps(r)+'\n' for r in rows))
    monkeypatch.setattr(owned.broader,'verify',corrupt)
    with pytest.raises((ValueError, FileNotFoundError)): owned.verify(args)
    assert not (args.output/'owned_admission.json').exists()


def test_existing_output_not_reused(setup):
    args,_,_=setup
    args.output.mkdir()
    with pytest.raises(FileExistsError): owned.verify(args)


def test_real_checker_row_shapes(setup,monkeypatch):
    from harness.proof_fragment_check import certify_fragment as repair
    from harness.proof_full_fragment_check import certify_fragment as full
    args,_,_=setup
    def underlying(a):
        rows=[]
        for i in range(36):
            row=dict(id=str(i),split='train' if i<32 else 'development',
                certified=False,status='no_proof_fragment')
            if i in (0,32):
                result=(full if i==0 else repair)(
                    '---- MODULE M ----\nTHEOREM Target == TRUE\n','OBVIOUS','\n====\n',
                    theorem_name='Target',work_root=a.output/'checks'/str(i),timeout=30)
                row.update(fragment='OBVIOUS',raw_reply_sha256='fixture',
                    fragment_contract='full-proof-fragment-v1' if i==0 else 'legacy-repair')
                row.update(result)
            rows.append(row)
        (a.output/'rows.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
        owned.write(a.output/'summary.json',dict(verification_complete=True,requested_tasks=36))
    monkeypatch.setattr(owned.broader,'verify',underlying)
    owned.verify(args)
    assert json.loads((args.output/'owned_admission.json').read_text())['certified_tasks']==2
