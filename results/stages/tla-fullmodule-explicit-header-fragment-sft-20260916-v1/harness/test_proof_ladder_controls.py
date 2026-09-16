"""Acceptance regression tests for the real reference/FALSE control driver."""
import pytest
from tools import proof_ladder_controls as controls


def pair():
    task=dict(prefix='---- MODULE M ----\nTHEOREM T == TRUE\n',
        reference_fragment='BY SMT',suffix='\n====\n',theorem_name='T',dependency_sha256={})
    task['goal_offsets']=[task['prefix'].index('TRUE'),len(task['prefix'])-1]
    rows=[]
    for prefix,positive in ((task['prefix'],True),(controls.wrong_conclusion(task),False)):
        nested=dict(contract_version='full-proof-fragment-v1',dependency_sha256={},
            sha256=controls.sha((prefix+task['reference_fragment']+task['suffix']).encode()),
            timed_out=False,command=['tlapm','--strict','--nofp','M.tla'],
            status='pass' if positive else 'verifier_reject',certified=positive,
            returncode=0 if positive else 10,proved=1 if positive else 0,total=1,
            output='All 1 obligations proved.' if positive else '[ERROR]: 1/1 obligations failed.\nPROVE FALSE\n')
        rows.append(dict(contract_version=controls.VERSION,certified=positive,
            status='pass' if positive else 'unproved_obligation',sany=dict(status='pass'),tlaps=nested))
    return task,rows


def test_exact_pair():
    task,rows=pair()
    assert controls.pair_passes(task,*rows)


@pytest.mark.parametrize('change',[
    lambda rows:rows[1]['sany'].update(status='model_sany_reject'),
    lambda rows:rows[1].update(status='unmeasured_budget'),
    lambda rows:rows[1].update(certified=True),
    lambda rows:rows[0].update(certified=False),
    lambda rows:rows[0]['tlaps'].update(sha256='0'*64),
    lambda rows:rows[1]['tlaps'].update(output='Parse Error'),
    lambda rows:rows[1]['tlaps'].update(output='[ERROR]: 2/2 obligations failed.\nPROVE FALSE\n'),
    lambda rows:rows[1]['tlaps'].update(timed_out=True),
])
def test_wrong_rejection_never_validates_controls(change):
    task,rows=pair();change(rows)
    assert not controls.pair_passes(task,*rows)
