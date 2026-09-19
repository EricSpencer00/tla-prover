"""Mocked SANY/TLAPS ladder plus read-only historical diagnostics; no processes."""
import json
from pathlib import Path
import sys

import pytest

from harness import proof_ladder_check as ladder


PREFIX='---- MODULE M ----\nTHEOREM T == TRUE\n'
SUFFIX='\n====\n'


@pytest.fixture
def runtime(tmp_path,monkeypatch):
    jar=tmp_path/'tla2tools.jar';jar.write_bytes(b'fake pinned jar')
    monkeypatch.setattr(ladder.runner,'TLA2TOOLS',jar)
    monkeypatch.setattr(ladder.runner,'CLASSPATH',str(jar))
    monkeypatch.setattr(ladder.shutil,'which',lambda name:sys.executable)
    return tmp_path


def fake_tlaps(prefix,fragment,suffix,*,theorem_name,dependencies,work_root,timeout):
    work_root.mkdir(parents=True);path=work_root/'M.tla';path.write_text(prefix+fragment+suffix)
    hashes={}
    for dep in dependencies:
        data=dep.read_bytes();(work_root/dep.name).write_bytes(data);hashes[dep.name]=ladder.sha(data)
    output='[INFO]: All 1 obligations proved.\n'
    result=dict(contract_version=ladder.full.CONTRACT_VERSION,certified=True,status='pass',proved=1,total=1,
        returncode=0,timed_out=False,output=output,seconds=1.,workdir=str(work_root),candidate_path=str(path),
        sha256=ladder.sha(path.read_bytes()),dependency_sha256=hashes,
        command=[str(ladder.runner.TLAPM),'--strict','--nofp','--cache-dir',
                 str(work_root/'cache'),'M.tla'])
    (work_root/'input.json').write_text(json.dumps(dict(prefix=prefix,fragment=fragment,suffix=suffix,
        theorem_name=theorem_name,contract_version=ladder.full.CONTRACT_VERSION)))
    (work_root/'tlapm.log').write_text(output);(work_root/'result.json').write_text(json.dumps(result))
    return result


def invoke(runtime,**kwargs):
    return ladder.certify_fragment(PREFIX,'BY SMT',SUFFIX,theorem_name='T',work_root=runtime/'runs',**kwargs)


def test_shared_deadline_and_both_checks(runtime):
    now=[0.];calls=[]
    def sany(cmd,work,timeout):
        calls.append(('sany',timeout));now[0]+=3
        assert cmd[-2:]==['tla2sany.SANY','M.tla']
        assert any(s.startswith('-Djava.io.tmpdir=') for s in cmd)
        assert any(s.startswith('-DTLA-Library=') for s in cmd)
        assert (work/'M.tla').read_text()==PREFIX+'BY SMT'+SUFFIX
        return 0,'Semantic processing of module M\n',3.,False
    def tlaps(*args,**kwargs):
        calls.append(('tlaps',kwargs['timeout']));now[0]+=2
        return fake_tlaps(*args,**kwargs)
    result=invoke(runtime,run_command=sany,tlaps_checker=tlaps,clock=lambda:now[0])
    assert result['certified'] and result['status']=='pass'
    assert calls==[('sany',30),('tlaps',27)] and result['seconds']==5
    assert result['sany']['returncode']==0 and result['tlaps']['proved']==1
    assert json.loads((Path(result['workdir'])/'result.json').read_text())==result


@pytest.mark.parametrize('rc,output,timed_out,status',[
    (0,'Semantic errors:\n*** Errors: 2\nLevel error',False,'model_sany_reject'),
    (1,'Parse Error',False,'model_sany_reject'),
    (42,'Semantic errors:\n*** Errors: 2',False,'unmeasured_unknown'),
    (0,'*** Errors: 1\nCannot find source file Missing.tla',False,'unmeasured_infrastructure'),
    (1,'java.lang.ClassNotFoundException',False,'unmeasured_infrastructure'),
    (1,'unknown diagnostic',False,'unmeasured_unknown'),
    (0,'Semantic processing of module Other',False,'unmeasured_unknown'),
    (0,'Semantic processing of module M\nFatal errors',False,'unmeasured_unknown'),
    (0,'Semantic processing of module M',True,'unmeasured_timeout'),
])
def test_sany_failure_never_calls_tlaps(runtime,rc,output,timed_out,status):
    def forbidden(*args,**kwargs):raise AssertionError('TLAPS must not run')
    result=invoke(runtime,run_command=lambda *args:(rc,output,1.,timed_out),tlaps_checker=forbidden)
    assert result['status']==status and not result['certified'] and result['tlaps'] is None
    assert result['sany']['returncode']==rc and result['sany']['output']==output


def test_budget_depleted_after_sany(runtime):
    now=[0.]
    def sany(*args):now[0]=30.;return 0,'Semantic processing of module M',30.,False
    def forbidden(*args,**kwargs):raise AssertionError('No TLAPS deadline remains')
    result=invoke(runtime,clock=lambda:now[0],run_command=sany,tlaps_checker=forbidden)
    assert result['sany']['status']=='pass' and result['status']=='unmeasured_budget'
    assert not result['certified'] and result['tlaps'] is None


def test_late_tlaps_result_cannot_certify(runtime):
    now=[0.]
    def tlaps(*args,**kwargs):now[0]=31.;return fake_tlaps(*args,**kwargs)
    result=invoke(runtime,clock=lambda:now[0],run_command=lambda *a:(0,'Semantic processing of module M',0.,False),tlaps_checker=tlaps)
    assert result['tlaps']['certified'] and not result['certified'] and result['status']=='unmeasured_budget'


def test_exact_dependency_copies(runtime):
    dep=runtime/'Defs.tla';dep.write_text('---- MODULE Defs ----\nD == TRUE\n====\n')
    result=invoke(runtime,dependencies=[dep],run_command=lambda *a:(0,'Semantic processing of module M',0.,False),tlaps_checker=fake_tlaps)
    assert result['certified']
    assert result['dependency_sha256']=={'Defs.tla':ladder.sha(dep.read_bytes())}


@pytest.mark.parametrize('body',['THEOREM Leak == TRUE','AXIOM Leak == FALSE','LEMMA == TRUE'])
def test_custom_unproved_dependency_rejected_before_sany(runtime,body):
    dep=runtime/'Bad.tla';dep.write_text('---- MODULE Bad ----\n'+body+'\n====\n')
    def forbidden(*args):raise AssertionError('No subprocess allowed')
    result=invoke(runtime,dependencies=[dep],run_command=forbidden)
    assert result['status']=='contract_reject' and result['sany']['status']=='not_run' and result['tlaps'] is None


def test_tlaps_artifact_tampering_is_unmeasured(runtime):
    def bad(*args,**kwargs):
        result=fake_tlaps(*args,**kwargs)
        Path(result['candidate_path']).write_text('TRUE')
        return result
    result=invoke(runtime,run_command=lambda *a:(0,'Semantic processing of module M',0.,False),tlaps_checker=bad)
    assert not result['certified'] and result['status']=='unmeasured_provenance'


def test_tlaps_assertion_stays_unknown(runtime):
    def assertion(*args,**kwargs):
        result=fake_tlaps(*args,**kwargs)
        result.update(certified=False,status='verifier_reject',proved=0,total=0,returncode=3,output='Assertion failed\n')
        work=Path(result['workdir']);(work/'tlapm.log').write_text(result['output']);(work/'result.json').write_text(json.dumps(result))
        return result
    result=invoke(runtime,run_command=lambda *a:(0,'Semantic processing of module M',0.,False),tlaps_checker=assertion)
    assert not result['certified'] and result['status']=='unmeasured_checker_internal'


def test_conservative_audit_can_veto_apparent_success(runtime,monkeypatch):
    from tools import proof_outcome_audit
    monkeypatch.setattr(proof_outcome_audit,'classify_outcome',lambda *a,**k:
        dict(classification='unmeasured_unknown',measured_model_outcome=False,reward_eligible=False))
    result=invoke(runtime,run_command=lambda *a:(0,'Semantic processing of module M',0.,False),tlaps_checker=fake_tlaps)
    assert result['tlaps']['certified']
    assert not result['certified'] and result['status']=='unmeasured_unknown'


def test_mutated_sany_candidate_cannot_be_model_rejection(runtime):
    def sany(cmd,work,timeout):
        (work/'M.tla').write_text('changed')
        return 0,'Semantic errors:\n*** Errors: 1',1.,False
    result=invoke(runtime,run_command=sany)
    assert result['status']=='unmeasured_provenance' and not result['certified'] and result['tlaps'] is None


def test_unexpected_python_failure_has_saved_unmeasured_record(runtime):
    def crash(*args):raise AssertionError('unexpected checker wrapper assertion')
    result=invoke(runtime,run_command=crash)
    assert result['status']=='unmeasured_unknown' and not result['certified']
    assert json.loads((Path(result['workdir'])/'result.json').read_text())==result


@pytest.mark.parametrize('timeout',[0,31,float('nan'),float('inf')])
def test_single_bounded_deadline(runtime,timeout):
    with pytest.raises(ValueError):invoke(runtime,timeout=timeout)


def test_historical_temporal_level_diagnostics_read_only():
    root=Path(__file__).resolve().parents[1]/'results/runs/proof-fresh14-assertion-sany-20260905-v1'
    if not root.exists():pytest.skip('Historical diagnostics unavailable')
    for arm,module in [('base','AsyncTerminationDetection_proof'),('child','SyncTerminationDetection_proof')]:
        for kind in ('candidate','reference'):
            path=root/arm/kind/'sany.log';raw=path.read_bytes()
            # Prior wrapper did not retain rc. These are diagnostic-unit cases
            # with a supplied rc0, not retroactive raw-returncode certificates.
            status=ladder.classify_sany(0,raw.decode(),False,module)
            assert status==('model_sany_reject' if kind=='candidate' else 'pass')
            assert path.read_bytes()==raw


def test_known_sany_parse_abort_is_not_infrastructure():
    output='***Parse Error***\nWas expecting "Step number"\ntla2sany.semantic.AbortException\nCould not parse module M from file M.tla\n'
    assert ladder.classify_sany(0,output,False,'M')=='model_sany_reject'
    assert ladder.classify_sany(0,output+'java.lang.NullPointerException\n',False,'M')=='unmeasured_infrastructure'
    assert ladder.classify_sany(0,output,False,'Other')=='unmeasured_infrastructure'
    assert ladder.classify_sany(0,'tla2sany.semantic.AbortException',False,'M')=='unmeasured_infrastructure'
    assert ladder.classify_sany(42,output,False,'M')=='unmeasured_unknown'
    assert ladder.classify_sany(255,output,False,'M')=='model_sany_reject'
    assert ladder.classify_sany(255,'Parse Error',False,'M')=='unmeasured_unknown'


def test_known_sany_lexical_abort_is_model_rejection():
    output=('Lexical error at line 90, column 40.  Encountered: <EOF> after : ""\n'
            'Fatal errors while parsing TLA+ spec in file M.tla\n'
            'tla2sany.semantic.AbortException\n'
            'Could not parse module M from file M.tla\n')
    assert ladder.classify_sany(255,output,False,'M')=='model_sany_reject'


def test_actual_sany_parse_abort_diagnostics_read_only():
    root=Path(__file__).resolve().parents[1]/'results/runs/proof-ladder-fresh14-replay-20260906-v1'
    if not root.exists():pytest.skip('Historical replay unavailable')
    rows=[json.loads(line) for line in (root/'rows.jsonl').read_text().splitlines()]
    affected=[r for r in rows if r['status']=='unmeasured_infrastructure']
    assert len(affected)==6
    for row in affected:
        sany=row['sany'];path=Path(row['workdir'])/'sany.log';raw=path.read_bytes()
        assert raw.decode()==sany['output']
        assert ladder.classify_sany(sany['returncode'],raw.decode(),sany['timed_out'],Path(row['candidate_path']).stem)=='model_sany_reject'
        assert path.read_bytes()==raw
