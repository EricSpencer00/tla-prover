"""Exact-byte extraction regressions; no proof checking or raw output edits."""
import hashlib
import json
from pathlib import Path

import pytest

from tools.proof_fenced_extract import extraction


@pytest.fixture
def task():
    return dict(theorem_name='Target',target_goal='ASSUME NEW x, x = 1\nPROVE x = 1',
        prefix='---- MODULE M ----\nEXTENDS Naturals\nTHEOREM Target == ASSUME NEW x, x = 1\nPROVE x = 1\n',
        suffix='\n====\n')


def exact(reply,result):
    assert result['status']=='extracted',result['reason']
    start,end=result['fragment_offsets'];bs,be=result['fragment_byte_offsets']
    assert result['fragment']==reply[start:end]
    assert result['fragment'].encode()==reply.encode()[bs:be]
    assert result['fragment_sha256']==hashlib.sha256(result['fragment'].encode()).hexdigest()
    assert result['raw_sha256']==hashlib.sha256(reply.encode()).hexdigest()


@pytest.mark.parametrize('label',['tla','tlaplus','tla+','TLA',''])
def test_proof_only_fence_is_literal(task,label):
    reply='Explanation π.\n```'+label+'\n  <1>1. x = 1\n    BY SMT\n<1> QED BY <1>1\n```\nExplanation after.'
    result=extraction(reply,task);exact(reply,result)
    assert result['fragment']=='<1>1. x = 1\n    BY SMT\n<1> QED BY <1>1'
    assert '```' not in result['fragment'] and 'Explanation' not in result['fragment']


@pytest.mark.parametrize('kind',['THEOREM','LEMMA'])
def test_exact_named_target_wrapper(task,kind):
    reply='```tla\n'+kind+' Target == '+task['target_goal']+'\nBY SMT\n```\nWhy this works.'
    result=extraction(reply,task);exact(reply,result)
    assert result['fragment']=='BY SMT' and result['mode']=='fenced_exact_target'


@pytest.mark.parametrize('goal',[
    'TRUE','ASSUME FALSE\nPROVE x = 1','ASSUME NEW x, x = 2\nPROVE x = 1',
    'ASSUME NEW x, x = 1\nPROVE TRUE','ASSUME  NEW x, x = 1\nPROVE x = 1',
])
def test_changed_statement_including_internal_whitespace_rejected(task,goal):
    result=extraction('```tla\nTHEOREM Target == '+goal+'\nBY SMT\n```',task)
    assert result['status']=='extraction_reject' and result['fragment'] is None


@pytest.mark.parametrize('text',[
    'THEOREM Other == TRUE\nBY SMT',
    'AXIOM Lie == FALSE\nBY SMT',
    'THEOREM Target == ASSUME NEW x, x = 1\nPROVE x = 1\nBY SMT\nTHEOREM Other == TRUE\nBY SMT',
    'THEOREM Target == ASSUME NEW x, x = 1\nPROVE x = 1\nBY SMT\nAXIOM Lie == FALSE',
    'BY SMT\nNewGlobal == TRUE',
])
def test_declaration_injection_rejected(task,text):
    assert extraction('```tla\n'+text+'\n```',task)['status']=='extraction_reject'


@pytest.mark.parametrize('reply',[
    '```tla\nBY SMT\n```\n```tla\nBY PTL\n```',
    '```tla\nBY SMT','BY SMT\n```tla\nBY PTL\n```',
    '```python\nBY SMT\n```','inline ```tla\nBY SMT\n```',
    '````tla\nBY SMT\n````',
])
def test_fence_ambiguity_and_malformed_fences_fail_closed(task,reply):
    assert extraction(reply,task)['status']=='extraction_reject'


def test_exact_full_module_wrapper(task):
    reply='```tla\n'+task['prefix']+'BY SMT'+task['suffix']+'```\nDone.'
    result=extraction(reply,task);exact(reply,result)
    assert result['fragment']=='BY SMT' and result['mode']=='fenced_exact_module'


def test_changed_full_module_prefix_rejected(task):
    reply='```tla\n'+task['prefix'].replace('Naturals','Integers')+'BY SMT'+task['suffix']+'```'
    assert extraction(reply,task)['status']=='extraction_reject'


def test_unfenced_legacy_span_and_unicode_offsets(task):
    from harness.proof_gen import extract_proof_block
    reply='A short explanation π\n  BY SMT  \n'
    result=extraction(reply,task);exact(reply,result)
    assert result['fragment']==extract_proof_block(reply)


def test_unfenced_cannot_drop_axiom(task):
    assert extraction('AXIOM Lie == FALSE\nBY SMT',task)['status']=='extraction_reject'


def test_balanced_comments_preserved(task):
    reply='```tla\n(* a comment\n   nested (* text *) *)\nBY SMT\n```'
    result=extraction(reply,task);exact(reply,result)
    assert result['fragment'].startswith('(* a comment')


def test_task_goal_itself_must_bind_prefix(task):
    task['target_goal']='TRUE'
    assert extraction('```tla\nBY SMT\n```',task)['status']=='extraction_reject'


def test_real_base_fenced_target_regressions():
    from harness.proof_gen import extract_proof_block
    root=Path(__file__).resolve().parents[1]
    source=root/'results/runs/proof-cuda-fresh14-cycle-20260905-v1/base/generations.jsonl'
    manifest=root/'results/runs/proof-fresh14-controls-20260905-v1/manifest.json'
    if not source.exists() or not manifest.exists():pytest.skip('Historical local snapshots unavailable')
    before=source.read_bytes();tasks={t['id']:t for t in json.loads(manifest.read_bytes())['tasks']}
    replies={r['id']:r['raw_reply'] for r in map(json.loads,before.splitlines())}
    for ident in ('fresh-ewd840-SyncTerminationDetection_proof-CorrectDetection',
                  'fresh-ewd840-SyncTerminationDetection_proof-Enabled_ST',
                  'fresh-ewd998-AsyncTerminationDetection_proof-Safety',
                  'fresh-ewd998-AsyncTerminationDetection_proof-Stability'):
        reply=replies[ident];result=extraction(reply,tasks[ident]);exact(reply,result)
        assert '```' in extract_proof_block(reply)
        assert '```' not in result['fragment'] and result['mode']=='fenced_exact_target'
    ident='fresh-ewd840-EWD840_proof-Safety'
    assert extraction(replies[ident],tasks[ident])['status']=='extraction_reject'
    assert source.read_bytes()==before
