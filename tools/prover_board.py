"""Publish one consistent, timestamped board; reject stale or concurrent edits.

The state is embedded in PROVER-BOARD.md, not kept in a second status file.
Use read to obtain a temporary draft and SHA; publish requires that exact SHA.
Historical board copies are evidence only and must never drive execution.
"""
import argparse
from copy import deepcopy
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BOARD = ROOT / 'docs/PROVER-BOARD.md'
MARKER = re.compile(r'<!-- prover-board-state\n(.*?)\n-->', re.S)
PHASES = {'local_work', 'queued', 'running', 'external_wait', 'unverified', 'complete'}
TASK_STATES = {'Done', 'In progress', 'Needs correction', 'Not ready', 'Blocked', 'Waiting'}


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def utc():
    return datetime.now(timezone.utc)


def validate(state, now=None):
    now = now or utc()
    observed = datetime.fromisoformat(state['verified_utc'].replace('Z', '+00:00'))
    if observed.tzinfo is None or not -30 <= (now-observed).total_seconds() <= 900:
        raise ValueError('Observation is future-dated or older than 15 minutes; refresh live evidence')
    if state['phase'] not in PHASES:
        raise ValueError('Unknown phase')
    job = state['active_job']
    if state['phase'] in {'queued', 'running'}:
        if not job or job['pbs_state'] != ('Q' if state['phase'] == 'queued' else 'R'):
            raise ValueError('Queued/running requires a matching live job handle and PBS state')
        if not all(job.get(k) for k in ('id', 'owner', 'host')):
            raise ValueError('Live job identity incomplete')
    elif job is not None:
        raise ValueError('Terminal/absent/unknown job cannot be listed as active')
    if state['phase'] == 'external_wait' and not state['external_blocker']:
        raise ValueError('External wait requires a concrete evidenced dependency')
    if not state['owner'] or not state['next_action'] or not state['observation_evidence']:
        raise ValueError('Owner, evidence, and next action are required')
    ids = [t['id'] for t in state['tasks']]
    if len(ids) != len(set(ids)) or any(t['state'] not in TASK_STATES for t in state['tasks']):
        raise ValueError('Duplicate task ID or unsupported state')
    if any(not t['evidence'] for t in state['tasks']):
        raise ValueError('Every task needs evidence or explicit missing evidence')
    # Block comment termination/Markdown table injection from state fields.
    if '-->' in json.dumps(state) or any('|' in str(v) or '\n' in str(v)
            for t in state['tasks'] for v in t.values()):
        raise ValueError('Invalid board delimiter in a field')


def render(state):
    job = state['active_job']
    handle = 'none' if job is None else f"`{job['id']}` ({job['pbs_state']}, {job['host']}, owner {job['owner']})"
    lines = ['# TLA Prover work board', '',
        'This is the only execution board. It records verified observations, not continuous live state. '
        'Recheck ownership before acting; if a check fails, record unverified instead of carrying forward a live claim.', '',
        '## Current execution', '',
        f"- Revision: {state['revision']}", f"- Verified UTC: {state['verified_utc']}",
        f"- Owner: {state['owner']}", f"- Phase: {state['phase']}", f'- Active job: {handle}',
        f"- Observation evidence: {state['observation_evidence']}",
        f"- Latest completed result: {state['last_result']}",
        f"- Local work: {state['local_work']}",
        f"- External blocker: {state['external_blocker'] or 'none verified'}",
        f"- Next action: {state['next_action']}", '', '## Objective and evidence rules', '',
        'Reach the frozen gates in order: 100% SANY, applicable TLC, non-vacuous intended behavior, '
        'then actual TLAPS proofs. See [the frozen contract](PROVER-GOAL-2026-09-05.md). '
        'A completed diagnostic or checkpoint is not acceptance. Preserve original receipts and denominators.', '',
        '## Tasks', '', '| ID | State | Task | Evidence / remaining requirement |',
        '| --- | --- | --- | --- |']
    for task in state['tasks']:
        lines.append('| ' + ' | '.join(str(task[k]) for k in ('id', 'state', 'task', 'evidence')) + ' |')
    lines += ['', '## Decisions', ''] + ['- '+d for d in state['decisions']]
    lines += ['', '## Board maintenance', '',
        '- Use `python3 tools/prover_board.py read --draft /tmp/prover-board-draft.json` to read state and its SHA. '
        'Refresh facts, edit that temporary draft, then publish with the returned `--expected-sha`.',
        '- Publish immediately after submission, start, exit, receipt collection, diagnosis, repair, or next-action change; '
        'publish before the next side effect and before handing off or archiving. Keep one owner and one active experiment.',
        '- `python3 tools/prover_board.py check` must pass before a final handoff. '
        'Concurrent edits require rereading and reconciling; never force an old draft over newer evidence.',
        '- Do not prepend handoffs, append duplicate checks, invent timestamps, or paste active jobs into the recurring prompt. '
        'Memory is only a pointer to this board. An unchanged external wait can refresh the timestamp without a new narrative.',
        '- If there is a local implementation defect, phase is local_work even when a later external action also needs approval. '
        'Fix authorized local work before treating that external action as the only blocker.', '',
        '## Historical evidence', '',
        'These snapshots preserve old statements, including mistakes. They are not current instructions.', '']
    lines += ['- '+path for path in state['history']]
    lines += ['', '<!-- prover-board-state', json.dumps(state, indent=2), '-->', '']
    return '\n'.join(lines)


def parse(raw):
    text = raw.decode()
    matches = MARKER.findall(text)
    if len(matches) != 1:
        raise ValueError('Board must contain exactly one authoritative embedded state')
    state = json.loads(matches[0])
    if render(state) != text:
        raise ValueError('Board text diverges from its state; reconcile through publish')
    return state


def recover_embedded_state(raw):
    """Read only the authoritative state marker for a format-repair publication."""
    matches = MARKER.findall(raw.decode())
    if len(matches) != 1:
        return None
    try:
        return json.loads(matches[0])
    except json.JSONDecodeError:
        return None


def history_revision_floor():
    """Return the highest valid archived revision, if local board text was damaged."""
    history = ROOT / 'results/board-history'
    revisions = []
    for archived in history.glob('board-*.md') if history.exists() else ():
        state = recover_embedded_state(archived.read_bytes())
        if isinstance(state, dict) and isinstance(state.get('revision'), int):
            revisions.append(state['revision'])
    return max(revisions, default=0)


def publish(board, candidate, expected_sha):
    board = Path(board)
    with board.with_suffix('.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        old = board.read_bytes()
        if digest(old) != expected_sha:
            raise ValueError('Board changed since read; reread and reconcile instead of overwriting')
        try:
            prior = parse(old)
        except ValueError:
            # Preserve the marker and a valid archived sequence when repairing
            # handwritten board text; never silently restart at revision 1.
            prior = recover_embedded_state(old)
        state = deepcopy(candidate)
        prior_revision = prior.get('revision', 0) if prior else 0
        state['revision'] = max(prior_revision, history_revision_floor()) + 1
        validate(state)
        for path in state['evidence_files']:
            resolved = Path(path) if Path(path).is_absolute() else ROOT / path
            if not resolved.is_file():
                raise ValueError('Missing evidence file: ' + path)
        history = ROOT / 'results/board-history'
        history.mkdir(parents=True, exist_ok=True)
        changed = prior is None or {k:v for k,v in prior.items() if k not in ('revision','verified_utc')} != {
            k:v for k,v in state.items() if k not in ('revision','verified_utc')}
        if changed:
            archive = history / f'board-{expected_sha}.md'
            if not archive.exists():
                archive.write_bytes(old)
        fd, temporary = tempfile.mkstemp(prefix='.PROVER-BOARD-', dir=board.parent)
        try:
            with os.fdopen(fd, 'w') as stream:
                stream.write(render(state)); stream.flush(); os.fsync(stream.fileno())
            os.replace(temporary, board)
        finally:
            if os.path.exists(temporary):
                os.unlink(temporary)
        parse(board.read_bytes())
        return state


def main():
    p = argparse.ArgumentParser()
    p.add_argument('mode', choices=('read', 'publish', 'check'))
    p.add_argument('--draft', type=Path)
    p.add_argument('--expected-sha')
    args = p.parse_args()
    raw = BOARD.read_bytes()
    if args.mode == 'publish':
        if not args.draft or not args.expected_sha:
            p.error('publish requires --draft and --expected-sha')
        state = publish(BOARD, json.loads(args.draft.read_text()), args.expected_sha)
        print(json.dumps(dict(revision=state['revision'], sha256=digest(BOARD.read_bytes()))))
    else:
        state = parse(raw)
        if args.mode == 'check':
            validate(state)
        elif args.draft:
            args.draft.write_text(json.dumps(state, indent=2)+'\n')
        print(json.dumps(dict(revision=state['revision'], sha256=digest(raw),
                             verified_utc=state['verified_utc'], phase=state['phase'], active_job=state['active_job'])))


if __name__ == '__main__':
    main()
