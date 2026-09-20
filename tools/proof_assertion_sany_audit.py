#!/usr/bin/env python3
"""Four isolated SANY diagnostics: two crashing candidates and their controls."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.proof_cuda_eval import dump
from tools.proof_cuda_train import file_sha
from harness.runner import check_sany,TLA_LIBRARY,TLA2TOOLS

REPLAY=ROOT/'results/runs/proof-fresh14-extraction-replay-20260905-v1/rows.jsonl'
REPLAY_SHA='89602fd1de41ee02f184100dec8dea20e68c13bce0334ac1f6d6ffb8f6b8d18c'
CONTROLS=ROOT/'results/runs/proof-fresh14-controls-20260905-v1/controls.json'
CONTROLS_SHA='74915911b16faea4671e2d3837b340d139cd170b751ee075bd8481365a949926'


def identity():
    paths={Path(__file__),ROOT/'harness/runner.py',TLA2TOOLS,REPLAY,CONTROLS}
    paths.update(p for root in TLA_LIBRARY.split(':') for p in Path(root).rglob('*.tla') if p.is_file())
    java=shutil.which('java')
    if java is None:raise ValueError('Java unavailable')
    paths.add(Path(java).resolve())
    version=subprocess.run([java,'-version'],capture_output=True,text=True,timeout=15,check=True)
    return dict(files={str(p):file_sha(p) for p in sorted(paths)},java=java,
        java_version=version.stdout+version.stderr,scope='Pinned jar, configured TLA libraries and Java launcher/version; not all system dynamic libraries')


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    if file_sha(REPLAY)!=REPLAY_SHA or file_sha(CONTROLS)!=CONTROLS_SHA:raise ValueError('Immutable audit inputs changed')
    rows=[json.loads(l) for l in REPLAY.read_text().splitlines()]
    errors=[r for r in rows if r['audit']['classification']=='unmeasured_checker_internal']
    controls={r['id']:r for r in json.loads(CONTROLS.read_bytes()) if r['control']=='reference'}
    if {(r['arm'],r['id']) for r in errors}!={
        ('child','fresh-ewd840-SyncTerminationDetection_proof-Quiescent'),
        ('base','fresh-ewd998-AsyncTerminationDetection_proof-Stability')}:
        raise ValueError('Exact two observed assertions required')
    a.output=a.output.resolve();a.output.mkdir(parents=True,exist_ok=False)
    before=identity();dump(a.output/'identity_before.json',before);results=[]
    dump(a.output/'config.json',dict(requested_checks=4,timeout=30,model_sampling=False,training_authorized=False,
        hypothesis='SANY independently diagnoses invalid temporal levels behind observed TLAPM assertions',
        stop='Two candidate/control pairs; no statement changes, no reclassification from a nonzero exit alone'))
    for error in errors:
        for label,row in (('candidate',error),('reference',controls[error['id']])):
            work=a.output/error['arm']/label;work.mkdir(parents=True,exist_ok=False)
            source=Path(row['candidate_path'])
            if file_sha(source)!=row['sha256']:raise ValueError('Raw checked module changed')
            shutil.copyfile(source,work/source.name)
            for name,h in row['dependency_sha256'].items():
                dep=Path(row['workdir'])/name
                if file_sha(dep)!=h:raise ValueError('Raw dependency changed')
                shutil.copyfile(dep,work/name)
            status,log,seconds=check_sany(work/source.name,work,30)
            (work/'sany.log').write_text(log)
            results.append(dict(arm=error['arm'],id=error['id'],kind=label,status=status,seconds=seconds,
                module_sha256=row['sha256'],dependency_sha256=row['dependency_sha256'],log_path=str(work/'sany.log')))
            dump(a.output/'rows.json',results)
    after=identity();dump(a.output/'identity_after.json',after)
    dump(a.output/'summary.json',dict(requested_checks=4,completed_checks=len(results),identity_stable=before==after,
        diagnostic_complete=before==after and len(results)==4,training_authorized=False,
        scope='Four diagnostic module parses only; not full14 SANY reliability or a TLAPS proof result'))
    if before!=after:raise ValueError('Diagnostic runtime changed')


if __name__=='__main__':main()
