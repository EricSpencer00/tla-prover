#!/usr/bin/env python3
"""Real fixed14 reference/FALSE controls for the new SANY-first proof gate."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from harness import runner
from harness.proof_ladder_check import certify_fragment,VERSION
from tools.proof_breadth26_manifest import wrong_conclusion,valid_pair,selection_digest
from tools.proof_fresh_selection import construct,identity as selection_identity
from tools.proof_whole_packet import dump,sha

SOURCES=('tools/proof_ladder_controls.py','harness/proof_ladder_check.py',
    'harness/proof_full_fragment_check.py','tools/proof_outcome_audit.py',
    'tools/proof_breadth26_manifest.py')


def identity(selection):
    java=shutil.which('java')
    if java is None:raise ValueError('Java unavailable')
    version=subprocess.run([java,'-version'],capture_output=True,text=True,check=True,timeout=15)
    paths={ROOT/p for p in SOURCES}|{Path(java).resolve(),Path(runner.TLA2TOOLS).resolve()}
    return dict(selection=selection_identity(selection),
        files={str(p):sha(p.read_bytes()) for p in sorted(paths)},
        java_version=version.stdout+version.stderr,
        scope='Full TLAPS libraries/backends plus SANY jar and Java launcher/version; not all system dynamic libraries')


def pair_passes(task,good,bad):
    return (good.get('certified') is True and bad.get('certified') is False
        and good.get('status')=='pass' and bad.get('status')=='unproved_obligation'
        and all(r.get('contract_version')==VERSION and r.get('sany',{}).get('status')=='pass'
                and isinstance(r.get('tlaps'),dict) for r in (good,bad))
        and valid_pair(task,good['tlaps'],bad['tlaps']))


def run(output):
    selection=construct()
    if len(selection['tasks'])!=14 or any(t['rejection_reasons'] for t in selection['tasks']):
        raise ValueError('All original14 frozen tasks required')
    output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    dump(output/'selection.json',selection)
    dump(output/'config.json',dict(contract=VERSION,requested_controls=28,requested_pairs=14,
        timeout=30,seconds=1000,selection_sha256=selection_digest(selection),
        hypothesis='All fixed human references pass SANY and strict TLAPS; conclusion-only FALSE controls pass SANY and fail exactly their intended obligation',
        stop='28 controls or1000seconds; retain all outcomes, no population reduction',
        training_authorized=False,model_sampling=False))
    for name in SOURCES:
        dest=output/'code'/name;dest.parent.mkdir(parents=True,exist_ok=True)
        dest.write_bytes((ROOT/name).read_bytes())
    rows=[];outcomes=[];started=time.monotonic()
    def read_identity():
        try:return identity(selection)
        except Exception as exc:return dict(identity_error=type(exc).__name__+': '+str(exc))
    before=read_identity();dump(output/'identity_before.json',before)
    def summary(final=False,stable=False):
        return dict(status='completed' if final else 'running',requested_controls=28,
            ledgered_controls=len(rows),requested_pairs=14,ledgered_pairs=len(outcomes),
            sany_pass=sum(r.get('sany',{}).get('status')=='pass' for r in rows),
            positive_certified=sum(r.get('certified') is True and r['control']=='reference' for r in rows),
            accepted_pairs=sum(o['passed'] for o in outcomes) if stable else 0,
            identity_stable=stable if final else None,
            controls_passed=final and stable and len(outcomes)==14 and all(o['passed'] for o in outcomes),
            training_authorized=False,seconds=time.monotonic()-started)
    dump(output/'summary.json',summary())
    for task in selection['tasks']:
        pair=[]
        for label in ('reference','wrong_conclusion'):
            remaining=1000-(time.monotonic()-started)
            if 'identity_error' in before:
                result=dict(status='unmeasured_identity',certified=False,reason=before['identity_error'])
            elif remaining<1:
                result=dict(status='unmeasured_budget',certified=False)
            else:
                prefix=task['prefix'] if label=='reference' else wrong_conclusion(task)
                result=certify_fragment(prefix,task['reference_fragment'],task['suffix'],
                    theorem_name=task['theorem_name'],dependencies=tuple(map(Path,task['dependencies'])),
                    work_root=output/'controls'/task['id']/label,timeout=min(30,remaining))
            row=dict(result,id=task['id'],control=label,training_authorized=False)
            pair.append(row);rows.append(row);dump(output/'rows.json',rows)
            dump(output/'summary.json',summary())
        outcomes.append(dict(id=task['id'],passed=bool(pair_passes(task,*pair))))
        dump(output/'outcomes.json',outcomes)
    after=read_identity();dump(output/'identity_after.json',after)
    stable='identity_error' not in before and before==after
    result=summary(True,stable);dump(output/'summary.json',result)
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    result=run(parser.parse_args().output)
    print(json.dumps(result))
    if not result['controls_passed']:raise SystemExit(1)
