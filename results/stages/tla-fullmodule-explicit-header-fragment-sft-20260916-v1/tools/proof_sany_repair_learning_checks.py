"""Matched TRAIN/DEV40 and selected TRAIN2 repair checks; separate denominators."""
from pathlib import Path
import time

from tools import proof_sumsequence_proof_rl_checks as checks
from tools.proof_cuda_train import dump
from tools.proof_cuda_eval import digest, sha

PHASES = ('greedy40', 'repair2')
LIMITS = {'greedy40': 2500, 'repair2': 180}
COUNTS = {'greedy40': 40, 'repair2': 2}
PARENT_SHA = '1bb603f605ddc0307631b0db4bda3fdfa109b5e0493f4508db05334deff87ee2'
REPAIR_IDS = ('breadth-ReachabilityProofs-Reachable1', 'sumsequence-Lemma3')


def validate_inputs(tasks, arms, policies):
    if set(tasks) != set(PHASES) or set(arms) != {'parent', 'child'}:
        raise ValueError('Two separate phases and both matched arms required')
    if (set(policies) != {'parent', 'child'} or policies['parent'] != PARENT_SHA
            or policies['child'] == PARENT_SHA or len(policies['child']) != 64
            or any(c not in '0123456789abcdef' for c in policies['child'])):
        raise ValueError('Actual immutable1bb6 parent and distinct child required')
    for phase in PHASES:
        ids = [t['id'] for t in tasks[phase]]
        if len(ids) != COUNTS[phase] or len(set(ids)) != len(ids):
            raise ValueError('Complete distinct original task denominator required')
        for arm in arms:
            if set(arms[arm]) != set(PHASES) or [r['id'] for r in arms[arm][phase]] != ids:
                raise ValueError('Exact matched ordered raw outputs required')
    if tuple(t['id'] for t in tasks['repair2']) != REPAIR_IDS:
        raise ValueError('Exact selected two repair targets required')
    original = {t['id']: t for t in tasks['greedy40']}
    if any(t != original.get(t['id']) or t['split'] != 'train' for t in tasks['repair2']):
        raise ValueError('Repairs retain original immutable TRAIN task bindings')


def summarize(rows, complete):
    if len(rows) != 84 or len({(r['arm'], r['phase'], r['id']) for r in rows}) != 84:
        raise ValueError('All84 unique requested keys required')
    if any(r[f] is not None and (type(r[f]) is not int or r[f] not in (0, 1))
           for r in rows for f in ('sany', 'proof')):
        raise ValueError('Only binary or explicitly unknown outcomes allowed')
    result = dict(complete=complete, requested_outputs=84, phases={},
                  original_denominator=40, repair_denominator=2, pooled_score=False,
                  generalization_claim=False, gate_claim=False, training_authorized=False)
    for phase in PHASES:
        entry = dict(requested_per_arm=COUNTS[phase], arms={}, paired={})
        for arm in ('parent', 'child'):
            chosen = [r for r in rows if r['phase'] == phase and r['arm'] == arm]
            if len(chosen) != COUNTS[phase]:
                raise ValueError('Every phase retains its complete denominator')
            entry['arms'][arm] = dict(accounted=len(chosen),
                **{field + suffix: sum(r[field] == value if value is not None else r[field] is None
                                      for r in chosen)
                   for field in ('sany', 'proof')
                   for suffix, value in (('_pass', 1), ('_reject', 0), ('_unknown', None))},
                generation_caps=sum(r['finish_reason'] == 'token_limit' for r in chosen),
                generation_timeouts=sum(r['finish_reason'] == 'time_limit' for r in chosen))
            populations = ({'original_train': chosen[:32], 'original_development': chosen[32:36],
                            'new_train': chosen[36:]} if phase == 'greedy40' else {'selected_train_repairs': chosen})
            entry['arms'][arm]['per_population'] = {
                name: dict(requested=len(group), sany_pass=sum(r['sany'] == 1 for r in group),
                           proof_pass=sum(r['proof'] == 1 for r in group),
                           sany_unknown=sum(r['sany'] is None for r in group),
                           proof_unknown=sum(r['proof'] is None for r in group))
                for name, group in populations.items()}
        for field in ('sany', 'proof'):
            paired = {k: [] for k in ('gains', 'losses', 'unknown', 'unchanged')}
            left = {r['id']: r[field] for r in rows if r['phase'] == phase and r['arm'] == 'parent'}
            right = {r['id']: r[field] for r in rows if r['phase'] == phase and r['arm'] == 'child'}
            if left.keys() != right.keys():
                raise ValueError('Matched phase task identities required')
            for ident, before in left.items():
                after = right[ident]
                label = ('unknown' if before is None or after is None else
                         'gains' if after > before else 'losses' if after < before else 'unchanged')
                paired[label].append(ident)
            entry['paired'][field] = paired
        result['phases'][phase] = entry
    return result


def evaluate(tasks, arms, policies, current, output, *, checker=checks.check, clock=time.monotonic):
    validate_inputs(tasks, arms, policies)
    output = Path(output)
    rows = [dict(arm=arm, phase=phase, id=t['id'], split=t['split'], policy_sha256=policies[arm],
                 raw_row_sha256=digest(raw), finish_reason=raw.get('finish_reason'),
                 sany=None, proof=None, status='unattempted', evidence=None)
            for arm in ('parent', 'child') for phase in PHASES
            for t, raw in zip(tasks[phase], arms[arm][phase])]
    dump(output / 'rows.json', rows)
    complete = True
    by_key = {(r['arm'], r['phase'], r['id']): r for r in rows}
    for arm in ('parent', 'child'):
        for phase in PHASES:
            started = clock()
            for task, raw in zip(tasks[phase], arms[arm][phase]):
                row = by_key[arm, phase, task['id']]
                if raw.get('finish_reason') != 'eos':
                    row['status'] = 'unmeasured_generation'
                elif clock() - started > LIMITS[phase] - 61:
                    row['status'] = 'unmeasured_budget'; complete = False
                else:
                    value = checker(task, raw['raw_reply'], output / 'checks' / arm / phase / task['id'], current)
                    row.update(sany=value['sany'], proof=value['proof'], status=value['status'], evidence=value)
                dump(output / 'rows.json', rows)
                dump(output / 'summary.json', summarize(rows, False))
            if clock() - started > LIMITS[phase]:
                complete = False
    return rows, summarize(rows, complete)


def audit_rows(tasks, arms, policies, rows, current, output):
    validate_inputs(tasks, arms, policies)
    expected = [(arm, phase, t['id']) for arm in ('parent', 'child') for phase in PHASES for t in tasks[phase]]
    if [(r['arm'], r['phase'], r['id']) for r in rows] != expected:
        raise ValueError('Exact complete84 ordered keys required')
    indexed = {(r['arm'], r['phase'], r['id']): r for r in rows}
    for arm in ('parent', 'child'):
        for phase in PHASES:
            for task, raw in zip(tasks[phase], arms[arm][phase]):
                row = indexed[arm, phase, task['id']]
                if (row['policy_sha256'] != policies[arm] or row['split'] != task['split']
                        or row['raw_row_sha256'] != digest(raw) or row['finish_reason'] != raw.get('finish_reason')):
                    raise ValueError('Immutable raw output/policy/task linkage changed')
                if raw.get('finish_reason') != 'eos' or row['status'] == 'unmeasured_budget':
                    if any(row[k] is not None for k in ('sany', 'proof', 'evidence')):
                        raise ValueError('Unknown generation or budget cannot be scored')
                    continue
                value = row['evidence']; extraction = checks.extract(task, raw['raw_reply'])
                if value is None or value['extraction'] != extraction or value['raw_reply_sha256'] != sha(raw['raw_reply'].encode()):
                    raise ValueError('Actual original task extractor/raw reply required')
                if extraction['fragment'] is None:
                    if any(value[k] != v for k, v in dict(sany=0, proof=0, status='model_extraction', evidence=None).items()):
                        raise ValueError('Exact extraction rejection required')
                else:
                    checks.audit_check(task, extraction['fragment'], value['evidence'],
                                       Path(output) / 'checks' / arm / phase / task['id'], current)
                    if any(value[k] != value['evidence'][k] for k in ('sany', 'proof', 'status')):
                        raise ValueError('Raw checker classification differs')
                if any(row[k] != value[k] for k in ('sany', 'proof', 'status')):
                    raise ValueError('Final classification differs from raw checker')
