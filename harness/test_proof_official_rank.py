import hashlib
import json
from pathlib import Path
import pytest
from tools.proof_official_extension import build_task
from tools.proof_official_rank import freeze_tasks, preflight_pool, dispatch, summary


@pytest.fixture
def manifest(tmp_path):
    raw = b'---- MODULE 2_Test ----\r\nF == TRUE\r\nTHEOREM Target == TRUE\r\n====\r\n\\* history\r\n'
    source = tmp_path/'source.tla'
    source.write_bytes(raw)
    official = [dict(id=str(i), category='math' if i else 'protocol', module_file='source.tla',
                theorem_name='Target', sha256=hashlib.sha256(raw).hexdigest()) for i in range(119)]
    original = tmp_path/'official.json'
    original.write_text(json.dumps(official))
    tasks = []
    for entry in official:
        task = build_task(entry, tmp_path)
        task.update(library_sha256={}, symbolic_candidates=['OBVIOUS','BY DEF F'], smt_visible=False,
                    retrieval=dict(visible_facts=[],ranked_imported_facts=[]))
        tasks.append(task)
    data = dict(tasks=tasks, official_manifest_path=str(original), source_aware_backends=True,
                official_manifest_sha256=hashlib.sha256(original.read_bytes()).hexdigest())
    path = tmp_path/'prepared.json'
    path.write_text(json.dumps(data))
    return path


def test_full_population_small_pool_source_and_fragment_newline(manifest):
    frozen = freeze_tasks(manifest)
    assert len(frozen) == 119
    task = frozen[0]
    assert task['candidates'] == ['\nOBVIOUS','\nBY DEF F']
    assert task['scoring_candidates'] == ['OBVIOUS','BY DEF F']
    assert (task['prefix']+task['suffix']).encode() == Path(task['source_path']).read_bytes()
    assert '\n<PROOF_HOLE>' in task['prompt']
    assert 'reference_fragment' not in task
    assert 'symbolic_candidates' not in task['prompt']


@pytest.mark.parametrize('change', ['drop','duplicate','category','target','proof','context','self_citation','injected_answer'])
def test_identity_and_answer_guards(manifest, change):
    data = json.loads(manifest.read_bytes())
    if change == 'drop': data['tasks'].pop()
    elif change == 'duplicate': data['tasks'][-1]['id'] = '0'
    elif change == 'category': data['tasks'][0]['category'] = 'other'
    elif change == 'target': data['tasks'][0]['theorem_name'] = 'Different'
    elif change == 'proof': data['tasks'][0]['prefix'] += '\nBY Answer'
    elif change == 'self_citation': data['tasks'][0]['symbolic_candidates'] = ['BY Target']
    elif change == 'injected_answer': data['tasks'][0]['symbolic_candidates'] = ['BY HiddenAnswer']
    elif change == 'context':
        data['tasks'][0]['retrieval']['visible_facts'] = [dict(name='Target', statement='TRUE')]
    manifest.write_text(json.dumps(data))
    with pytest.raises(ValueError): freeze_tasks(manifest)


def test_context_budget_records_full_pool_unranked(monkeypatch):
    import tools.proof_official_rank as rank
    def encode(tokenizer, prompt, candidate, budget):
        assert budget > 8192
        return dict(input_ids=list(range(8193 if candidate=='long' else 5)), labels=[],
                    response_tokens=2, prompt_tokens=3)
    monkeypatch.setattr(rank, 'encode_candidate', encode)
    encodings, status, reason = preflight_pool(None, dict(prompt='p', candidates=['short','long']), 8192)
    assert len(encodings) == 2 and len(encodings[1]['input_ids']) == 8193
    assert status == 'preflight_context_budget'
    assert 'entire pool unranked' in reason


def test_separator_is_fixed_scaffolding_not_token_boundary(monkeypatch):
    import tools.proof_official_rank as rank
    def encode(tokenizer, prompt, candidate, budget):
        assert candidate == 'BY SMT'
        return dict(input_ids=[1,2,3], labels=[-100,2,3])
    monkeypatch.setattr(rank, 'encode_candidate', encode)
    encoded, status, _ = preflight_pool(None, dict(prompt='p', candidates=['\nBY SMT'],
                                        scoring_candidates=['BY SMT']), 8192)
    assert status == 'ready'
    assert encoded[0]['candidate_fragment'] == '\nBY SMT'
    assert encoded[0]['scoring_text'] == 'BY SMT'


def test_dispatch_round_robin_and_under_four_pools():
    tasks = [dict(id=str(i)) for i in range(119)]
    rankings = {str(i):[dict(candidate_index=0),dict(candidate_index=1)] for i in range(119)}
    calls = [(t['id'],r) for t,r,_ in dispatch(tasks,rankings)]
    assert calls[:119] == [(str(i),1) for i in range(119)]
    assert calls[119:] == [(str(i),2) for i in range(119)]


def test_category_and_total_denominator_with_unscored_tasks():
    tasks = [dict(id=str(i),category='protocol' if i<26 else 'math') for i in range(119)]
    scores = {'26':[]}
    checks = [dict(task='26',rank=2,certified=True)]
    result = summary(tasks, {}, scores, checks)
    assert result['requested_tasks'] == 119
    assert result['unranked_tasks'] == result['unchecked_tasks'] == 118
    assert result['top1_verified'] == 0 and result['top4_verified'] == 1
    assert result['by_category']['protocol']['requested'] == 26
    assert result['by_category']['math']['requested'] == 93
