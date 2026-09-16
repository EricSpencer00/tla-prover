from datetime import datetime, timedelta, timezone
import pytest

from tools.prover_board import digest, parse, publish, render, validate


def snapshot():
    return dict(revision=1, verified_utc=datetime.now(timezone.utc).isoformat(), owner='test',
                phase='local_work', active_job=None, observation_evidence='read-only observation',
                last_result='negative diagnostic', local_work='repair staged import', external_blocker=None,
                next_action='run staged smoke', tasks=[dict(id='TLA-06', state='In progress',
                task='repair', evidence='import failure')], decisions=[], history=[], evidence_files=[])


def test_rejects_terminal_job_as_active():
    state = snapshot()
    state.update(phase='running', active_job=dict(id='1', pbs_state='F', host='sophia', owner='test'))
    with pytest.raises(ValueError, match='matching live job'):
        validate(state)


def test_rejects_future_and_stale_observations():
    state = snapshot()
    for delta in (-16, 2):
        state['verified_utc'] = (datetime.now(timezone.utc)+timedelta(minutes=delta)).isoformat()
        with pytest.raises(ValueError, match='future-dated'):
            validate(state)


def test_rejects_competing_handwritten_handoff():
    state = snapshot()
    with pytest.raises(ValueError, match='diverges'):
        parse((render(state)+'\n## Run handoff\nactive job 1\n').encode())


def test_publish_preserves_newer_edits(tmp_path):
    board = tmp_path/'board.md'
    original = render(snapshot()).encode()
    board.write_bytes(original)
    concurrent = original+b'changed by another owner\n'
    board.write_bytes(concurrent)
    with pytest.raises(ValueError, match='changed since read'):
        publish(board, snapshot(), digest(original))
    assert board.read_bytes() == concurrent


def test_publish_updates_one_snapshot_and_preserves_prior_evidence(tmp_path, monkeypatch):
    from tools import prover_board
    monkeypatch.setattr(prover_board, 'ROOT', tmp_path)
    board = tmp_path/'board.md'
    original = render(snapshot()).encode()
    board.write_bytes(original)
    candidate = snapshot()
    candidate['next_action'] = 'verify repaired stage'
    published = publish(board, candidate, digest(original))
    assert published['revision'] == 2
    assert parse(board.read_bytes())['next_action'] == 'verify repaired stage'
    assert (tmp_path/'results/board-history'/f'board-{digest(original)}.md').read_bytes() == original


def test_publish_repairs_diverged_text_without_revision_rollback(tmp_path, monkeypatch):
    from tools import prover_board
    monkeypatch.setattr(prover_board, 'ROOT', tmp_path)
    board = tmp_path/'board.md'
    original_state = snapshot()
    original_state['revision'] = 144
    original = render(original_state).encode()
    damaged = original.replace(b'- Phase: local_work', b'- Phase: external_wait')
    board.write_bytes(damaged)
    candidate = snapshot()
    candidate['next_action'] = 'repair damaged board'
    published = publish(board, candidate, digest(damaged))
    assert published['revision'] == 145
    assert parse(board.read_bytes())['revision'] == 145
    assert (tmp_path/'results/board-history'/f'board-{digest(damaged)}.md').read_bytes() == damaged
