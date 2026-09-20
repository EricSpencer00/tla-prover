"""Fixed TRAIN20 free-generation diagnostic; no targets exported or launch approval."""
import argparse
import json
import os
from pathlib import Path
import sys

CPU_ENV={n:'4' for n in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS')}
os.environ.update(CPU_ENV,HF_HUB_OFFLINE='1',TRANSFORMERS_OFFLINE='1',TOKENIZERS_PARALLELISM='false')
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_fullmodule_learning_packet as training

sha=training.sha;digest=training.digest;file_sha=training.file_sha;load=training.load;dump=training.dump
INPUT=ROOT/'results/runs/proof-fullmodule-learning-packet-20260906-v2/train.json'
INPUT_SHA='a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c'
TOKENIZER=training.audit.framing.TOKENIZER
INDICES=tuple(i*126//19 for i in range(20))
POLICIES=dict(parent=training.PARENT_SHA,child='fba2768ed9a8f629f6496dc1ef72763b32fc339c74ba9075d1ffc53acd6c2d1d')
SOURCES=tuple(sorted(set(training.SOURCES)|{'tools/proof_fullmodule_train_probe_packet.py'}))
ROWS_SHA='37681a87c3d80ca4b6ef9ffd71cc23986ef9d72f2553d0b998803e2e1672befe'
TOKENIZER_SHA='7ab4e8d651bca3553486fe7f5894b2b770e0f6b3daebe0527d8d2c19f69baec9'
CONTRACT=dict(schema=1,kind='fixed_train20_fullmodule_autoregressive_probe',split='train',
    selection='floor(i*126/19), i=0..19, on original admitted127 order; no outcome-based selection',
    candidate_population=127,requested_tasks=20,requested_samples_per_arm=20,requested_samples=40,
    policies=POLICIES,do_sample=False,temperature=0.,num_beams=1,attempts_per_task=1,seed=20261010,
    max_new_tokens=16384,seconds_per_item=45,sampling_seconds_per_arm=900,supervisor_seconds=3420,
    max_gpu_memory_bytes=36*1024**3,truncation=False,optimizer_updates=0,
    training_authorized=False,launch_authorized=False,model_generation_performed=False,
    reference_answers_exported=False,protected_outcomes_used=False,gate2_claim=False,generalization_claim=False,
    proof_claim=False,tlc_claim=False,nonvacuity_claim=False,
    metric='Matched greedy TRAIN full-module syntax diagnostic; not teacher-forced loss or heldout evaluation',
    checkpoint_training_receipts_required=True,target_memory_admission_required=True)
FIELDS=set(CONTRACT)|{'training_input_sha256','selected_indices','tasks','tasks_sha256','tokenizer_files',
    'source_sha256','minimum_required_context','prompt_environment','cpu_environment','control_pins','audit_pins'}


def sources():return {n:file_sha(ROOT/n) for n in SOURCES}


def tokenizer_files():
    return {p.name:file_sha(p) for p in sorted(TOKENIZER.iterdir()) if p.is_file() and
        (p.suffix=='.json' or p.name in ('tokenizer.model','chat_template.jinja'))}


def select(raw):
    if sha(raw)!=INPUT_SHA:raise ValueError('Exact admitted TRAIN169 packet-v2 required')
    value=json.loads(raw);allrows=training.validate_training_packet(value)
    rows=allrows[42:];encodings=value['encodings'][42:]
    if len(rows)!=127:raise ValueError('Original admitted127 population required')
    candidates={r['id']:r for r in json.loads(value['audit_rows_bytes'])}
    tasks=[]
    for index in INDICES:
        row=rows[index];e=encodings[index];candidate=candidates[row['id'].removeprefix('w4-fullmodule:')]
        if row['split']!='train' or candidate['exclusions']['status']!='lexically_clear':
            raise ValueError('Only existing lexically clear TRAIN rows allowed')
        ids=e['input_ids'][:e['prompt_tokens']]
        if row['response'] in row['prompt']:raise ValueError('Target body leaked into inference prompt')
        tasks.append(dict(id=row['id'],split='train',fullmodule_index=index,training_index=42+index,
            module_name=candidate['raw']['module'],control_task_id=candidate['id'],audit_index=candidate['index'],
            original_training_row_sha256=digest(row),
            source_sha256=row['source_sha256'],response_sha256=row['response_sha256'],
            training_encoding_sha256=digest(e),audit_row_sha256=digest(candidate),
            prompt=row['prompt'],prompt_sha256=row['prompt_sha256'],rendered_prompt=e['rendered_prompt'],
            rendered_prompt_sha256=sha(e['rendered_prompt'].encode()),input_token_ids=ids,
            input_token_ids_sha256=digest(ids),input_tokens=len(ids),required_context=len(ids)+16384))
    return tasks


def validate_export(value):
    if (not isinstance(value,dict) or set(value)!=FIELDS or
        any(value.get(k)!=v or type(value.get(k)) is not type(v) for k,v in CONTRACT.items())):
        raise ValueError('Exact TRAIN-only diagnostic contract required')
    tasks=value['tasks']
    if (value['training_input_sha256']!=INPUT_SHA or value['selected_indices']!=list(INDICES) or
        len(tasks)!=20 or digest(tasks)!=ROWS_SHA or value['tasks_sha256']!=ROWS_SHA or
        digest(value['tokenizer_files'])!=TOKENIZER_SHA or value['source_sha256']!=sources()):
        raise ValueError('Frozen membership, source, tokenizer and full prompt bytes required')
    if (value['minimum_required_context']!=max(t['required_context'] for t in tasks) or
        value['minimum_required_context']>131072 or value['prompt_environment']!=training.audit.framing.PROMPT_ENV or
        value['cpu_environment']!=CPU_ENV or value['control_pins']!=training.CONTROL_PINS or value['audit_pins']!=training.controls.PINS):
        raise ValueError('Exact context and original syntax-control provenance required')
    return tasks


validate_packet=validate_export


def prepare():
    before=sources();raw=INPUT.read_bytes();tasks=select(raw)
    files=tokenizer_files()
    from transformers import AutoTokenizer
    tokenizer=AutoTokenizer.from_pretrained(TOKENIZER,local_files_only=True)
    for task in tasks:
        rendered=tokenizer.apply_chat_template([dict(role='user',content=task['prompt'])],tokenize=False,add_generation_prompt=True)
        ids=tokenizer(rendered,add_special_tokens=False,truncation=False)['input_ids']
        if (rendered!=task['rendered_prompt'] or ids!=task['input_token_ids'] or not ids or
            ids[0]!=tokenizer.bos_token_id or ids.count(tokenizer.bos_token_id)!=1):
            raise ValueError('Actual inference prefix differs from exact supervised training prefix')
    result=dict(CONTRACT,training_input_sha256=INPUT_SHA,selected_indices=list(INDICES),tasks=tasks,
        tasks_sha256=digest(tasks),tokenizer_files=files,source_sha256=before,
        minimum_required_context=max(t['required_context'] for t in tasks),
        prompt_environment=training.audit.framing.PROMPT_ENV,cpu_environment=CPU_ENV,
        control_pins=training.CONTROL_PINS,audit_pins=training.controls.PINS)
    validate_export(result)
    if before!=sources() or files!=tokenizer_files() or sha(INPUT.read_bytes())!=INPUT_SHA:
        raise ValueError('Input/source/tokenizer drift during preparation')
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    result=prepare();a.output.mkdir(parents=True,exist_ok=False);dump(a.output/'prompts.json',result)
    print(json.dumps(dict(requested_tasks=20,minimum_required_context=result['minimum_required_context'],
        prompts_sha256=file_sha(a.output/'prompts.json'),launch_authorized=False)))


if __name__=='__main__':main()
