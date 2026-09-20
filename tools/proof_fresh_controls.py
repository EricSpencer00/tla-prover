"""Bounded exact14 fresh-evaluation controls; never training admission."""
import copy
import math
from pathlib import Path
import time

from tools.proof_breadth26_manifest import wrong_conclusion,valid_pair,selection_digest
from harness.proof_full_fragment_check import certify_fragment
from tools.proof_whole_packet import dump,sha


def controls(selection,output,seconds=1000,timeout=30,checker=certify_fragment,*,identity):
    """Ledger all28 requested outcomes; admit evaluation only as a complete set.

    The caller supplies the complete runtime/source/exclusion attestation. Any
    exception, absent selection binding or identity drift prevents authorization.
    A final stable ledger may be complete accounting even when controls failed.
    """
    if (not math.isfinite(seconds) or not math.isfinite(timeout) or
            not 0<seconds<=1000 or not 0<timeout<=30):
        raise ValueError('Maximum1000 seconds total and30 seconds/control')
    tasks=selection.get('tasks',[])
    if (selection.get('requested_evaluation')!=14 or len(tasks)!=14 or
            len({t['id'] for t in tasks})!=14 or
            any(t.get('split')!='fresh_evaluation' or 'rejection_reasons' not in t for t in tasks) or
            selection.get('training_authorized',False) is not False or not callable(identity)):
        raise ValueError('Exactly14 fresh_evaluation tasks, no TRAIN, and explicit identity required')
    snapshot=copy.deepcopy(selection);tasks=snapshot['tasks'];expected=selection_digest(snapshot)
    output=Path(output)
    names=('controls.json','outcomes.json','summary.json','manifest.json','verifier_before.json','verifier_after.json')
    if any((output/name).exists() for name in names):raise ValueError('Control output artifacts must be new')
    output.mkdir(parents=True,exist_ok=True)
    started=time.monotonic();rows=[];outcomes=[];admitted=[]
    def identity_read():
        try:
            result=identity()
            if not isinstance(result,dict) or result.get('fresh_selection_sha256')!=expected:
                return dict(identity_error='Missing or mismatched fresh selection identity')
            return copy.deepcopy(result)
        except Exception as exc:
            return dict(identity_error=type(exc).__name__+': '+str(exc))
    def summary(final=False,stable=False):
        accounting=(len(rows)==28 and len(outcomes)==14)
        authorized=final and stable and accounting and len(admitted)==14
        return dict(status='completed' if final else 'running',requested_evaluation=14,requested_controls=28,
            ledgered_controls=len(rows),completed_controls=sum('command' in r for r in rows),
            evaluation_tasks_accounted=len(outcomes),admitted_evaluation=len(admitted) if final and stable else 0,
            admitted_task_ids=admitted[:] if final and stable else [],unadmitted_evaluation=14-(len(admitted) if final and stable else 0),
            verifier_identity_stable=stable if final else None,verification_complete=final and stable and accounting,
            complete_population=authorized,evaluation_authorized=authorized,training_authorized=False,
            elapsed_seconds=time.monotonic()-started)
    dump(output/'controls.json',rows);dump(output/'outcomes.json',outcomes);dump(output/'summary.json',summary())
    before=identity_read();dump(output/'verifier_before.json',before)
    valid_before='identity_error' not in before
    for task in tasks:
        pair=[]
        for label in ('reference','wrong_conclusion'):
            remaining=seconds-(time.monotonic()-started)
            if not valid_before:
                result=dict(status='identity_error',certified=False,reason=before['identity_error'])
            elif task['rejection_reasons']:
                result=dict(status='selection_reject',certified=False,reasons=task['rejection_reasons'])
            elif remaining<1:
                result=dict(status='unmeasured_budget',certified=False)
            else:
                try:
                    prefix=task['prefix'] if label=='reference' else wrong_conclusion(task)
                    result=checker(prefix,task['reference_fragment'],task['suffix'],theorem_name=task['theorem_name'],
                        dependencies=tuple(map(Path,task['dependencies'])),
                        work_root=output/'controls'/task['id']/label,timeout=min(timeout,remaining))
                    if not isinstance(result,dict):raise ValueError('Checker must return a result object')
                except Exception as exc:
                    result=dict(status='control_error',certified=False,reason=type(exc).__name__+': '+str(exc))
            row=dict(result,id=task['id'],control=label,split='fresh_evaluation',training_authorized=False)
            pair.append(row);rows.append(row)
            dump(output/'controls.json',rows);dump(output/'summary.json',summary())
        try:accepted=valid_before and not task['rejection_reasons'] and valid_pair(task,*pair)
        except (KeyError,ValueError,TypeError):accepted=False
        if accepted:admitted.append(task['id'])
        outcomes.append(dict(id=task['id'],split='fresh_evaluation',admitted=bool(accepted),
            training_authorized=False,control_statuses=[r.get('status','invalid_result') for r in pair]))
        dump(output/'outcomes.json',outcomes);dump(output/'summary.json',summary())
    after=identity_read();dump(output/'verifier_after.json',after)
    stable=(valid_before and 'identity_error' not in after and before==after and selection_digest(selection)==expected)
    if not stable:
        admitted=[]
        for outcome in outcomes:outcome.update(admitted=False,reason='verifier_source_or_selection_identity_changed')
        dump(output/'outcomes.json',outcomes)
    result=summary(final=True,stable=stable);dump(output/'summary.json',result)
    if result['evaluation_authorized']:
        manifest=copy.deepcopy(snapshot)
        manifest.update(kind='controlled_fresh14_evaluation',training_authorized=False,evaluation_authorized=True,
            admitted_evaluation=14,verification_complete=True,
            controls_sha256=sha((output/'controls.json').read_bytes()),outcomes_sha256=sha((output/'outcomes.json').read_bytes()),
            verifier_identity=before,negative_contract='preserve-assumptions-conclusion-only-FALSE-v1',
            reference_scope='Local checker controls only; evaluation references must never enter inference or TRAIN exports')
        dump(output/'manifest.json',manifest)
    return result
