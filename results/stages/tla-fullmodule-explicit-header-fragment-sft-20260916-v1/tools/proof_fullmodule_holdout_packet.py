"""Evaluation-only frozen Framing-A holdout30 packet; no oracle or model run.

Only descriptions and configuration signatures enter prompts. Canonical source,
dependency and wrapper bodies remain local oracle inputs, never model inputs.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys

CPU_ENV={n:'4' for n in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS')}
os.environ.update(CPU_ENV,HF_HUB_OFFLINE='1',TRANSFORMERS_OFFLINE='1',TOKENIZERS_PARALLELISM='false')
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from harness import gen_eval as framing,runner
from harness.loop_eval import wrapper_text_for

CORPUS=framing.DEFAULT_CORPUS
TOKENIZER=ROOT/'results/runs/proof-cuda-tokenizer-20260905-v2'
IDS=('2','5','13','14','15','30','32','37','41','55','86','95','105','106','121','128','131','132','133','135','141','142','143','148','158','168','174','181','183','191')
HOLDOUT_SHA='ecfc20533b9dc9a6e727ab989732310659d469eefbcc3705df72e3094ef54f78'
POLICIES=dict(parent='1bb603f605ddc0307631b0db4bda3fdfa109b5e0493f4508db05334deff87ee2',
    child='88660d5a17eab6ae23adf109e5619db0feb986254e8b46460899a528781cdde3')
PROMPT_ENV=dict(TLA_PROMPT_WRAPPER_AWARE='0',TLA_PROMPT_NO_REDEF='0',TLA_PROMPT_ARITY='0',GEN_EVAL_CONCURRENCY='1')
SOURCES=('harness/__init__.py','harness/decoding.py','harness/runner.py','harness/mutation.py',
    'harness/repair.py','harness/gen_eval.py','harness/loop_eval.py','tools/__init__.py',
    'tools/proof_fullmodule_holdout_packet.py')
COUNTS=dict(state_machine=23,library=4,proof_module=2,expected_violation=1)
# Filled from the immutable local corpus/config/tokenizer reconstruction before release.
INPUTS_SHA='4930d5a17f49e032873d0c242073857ba2a9423c10da064f27fd664fd6de6a33'
ROWS_SHA='6f7505922e4879a00ea9e0f9ab397e460d16812ff91582526aabb9437983f527'
CONTRACT=dict(schema=1,kind='frozen_fullmodule_holdout30_framing_A_preparation',split='official_holdout30',
    requested_tasks=30,requested_samples_per_arm=30,requested_samples=60,policies=POLICIES,
    max_new_tokens=16384,temperature=0.,do_sample=False,num_beams=1,attempts_per_task=1,
    truncation=False,optimizer_updates=0,model_generation_performed=False,launch_authorized=False,
    training_authorized=False,protected_failures_must_not_feed_training=True,
    reference_answers_exported=False,oracle_controls_performed=False,oracle_controls_required=30,
    target_memory_admission_required=True,gate2_claim=False,pass_at32_claim=False,
    tlc_claim=False,proof_claim=False,generalization_claim=False,g1_denominator=206,
    metric='paired greedy full-module SANY diagnostic only; not full Gate2 or corpus closure')
PREREQUISITES=['Actual30 canonical-oracle SANY controls with exact dependency/runtime evidence',
    'Actual known-bad SANY controls; no syntax acceptance inferred from metadata',
    'Full target checkpoint/training-receipt and16384-output peak-memory admission',
    'Explicit bounded matched-run launch decision']
DATA_ROLE='Protected official holdout30; evaluation only; no repairs, references or failures may feed training'
PACKET_FIELDS=set(CONTRACT)|{'holdout_sha256','prompt_environment','cpu_environment','population_counts','tasks',
    'inventories','source_sha256','minimum_required_context','prerequisites','data_role','g1_missing_source_ids','g1_source_inventory_count'}


def sha(raw):return hashlib.sha256(raw).hexdigest()
def digest(value):return sha(json.dumps(value,sort_keys=True,separators=(',',':')).encode())
def file_sha(path):return sha(Path(path).read_bytes())
def load(path):return json.loads(Path(path).read_bytes())


def environment():
    if any(os.environ.get(n,'1' if n=='GEN_EVAL_CONCURRENCY' else '0')!=v for n,v in PROMPT_ENV.items()):
        raise ValueError('Explicit historical Framing-A prompt flags required; do not silently change prompts')
    if framing.GEN_EVAL_CONCURRENCY!=1:raise ValueError('Imported generation concurrency drift')
    return dict(PROMPT_ENV)


def cfg_dirs():return [('override',ROOT/'corpus/configs/overrides'),('original',CORPUS/'cfg'),('draft',ROOT/'corpus/configs/drafts')]


def source_path(num):
    patched=ROOT/'corpus/configs/patches'/f'{num}.tla'
    return patched if patched.is_file() else CORPUS/'tla_files'/f'{num}.tla'


def wrapper_path(num,n2m,m2p):
    value=runner.POLICY.get(num,{}).get('wrapper')
    if not value:return None
    if 'file' in value:return ROOT/value['file']
    number=value['corpus_spec'];patch=ROOT/'corpus/configs/patches'/f'{number}.tla'
    return patch if patch.is_file() else m2p[n2m[number]]


def metadata(path):return dict(path=str(path.resolve()),sha256=file_sha(path))


def dependency_closure(text,module,m2p):
    seen={module};files={};frontier=runner.local_deps(text,m2p)-seen
    while frontier:
        name=min(frontier);frontier.remove(name)
        if name in seen:continue
        seen.add(name);path=source_path(m2p[name].stem);body=path.read_text()
        if runner.module_name(body)!=name:raise ValueError('Dependency module identity changed')
        files[str(path.resolve())]=file_sha(path)
        frontier|=runner.local_deps(body,m2p)-seen
    return dict(sorted(files.items()))


def inventories():
    files={framing.HOLDOUT_FILE,ROOT/'corpus/configs/populations.json',ROOT/'corpus/configs/policy.json'}
    files.update((CORPUS/'tla_files').glob('*.tla'))
    files.update(CORPUS/'descriptions'/f'{n}.json' for n in IDS)
    for _,directory in cfg_dirs():files.update(directory.glob('*.cfg'))
    files.update((ROOT/'corpus/configs/patches').glob('*.tla'))
    n2m,m2p=runner.build_module_index(CORPUS)
    for n in IDS:
        path=wrapper_path(n,n2m,m2p)
        if path is not None:files.add(path)
    tokenfiles=[p for p in TOKENIZER.iterdir() if p.is_file() and (p.suffix=='.json' or p.name in ('tokenizer.model','chat_template.jinja'))]
    return dict(inputs={str(p.resolve()):file_sha(p) for p in sorted(files)},
        tokenizer={p.name:file_sha(p) for p in sorted(tokenfiles)})


def sources():return {p:file_sha(ROOT/p) for p in SOURCES}


def population(num):
    if num in runner.PROOF_MODULES:return 'proof_module'
    if num in runner.LIBRARIES:return 'library'
    if num in runner.EXPECTED_VIOLATIONS:return 'expected_violation'
    return 'state_machine'


def make_rows(tokenizer):
    environment();ids,h=framing.holdout_specs_and_hash()
    if ids!=list(IDS) or h!=HOLDOUT_SHA:raise ValueError('Exact protected holdout30 membership required')
    n2m,m2p=runner.build_module_index(CORPUS);rows=[]
    for num in IDS:
        src=source_path(num);body=src.read_text();module=n2m[num]
        if body!=framing.canonical_spec_text(num,CORPUS) or runner.module_name(body)!=module:
            raise ValueError('Original numbered oracle source/patch precedence changed')
        desc=CORPUS/'descriptions'/f'{num}.json';cfg,label=framing._resolve_cfg(num,cfg_dirs())
        path=next(directory/f'{num}.cfg' for key,directory in cfg_dirs() if key==label)
        description=desc.read_text();wrap=wrapper_text_for(num,n2m,m2p);wp=wrapper_path(num,n2m,m2p)
        if (wp is None)!=(wrap is None) or (wp is not None and wp.read_text()!=wrap):raise ValueError('Wrapper context resolution changed')
        prompt=framing.build_generation_prompt(json.loads(description),cfg,module,wrap)
        # All enhancement flags are off. Oracle/wrapper text cannot influence the prompt.
        if prompt!=framing.build_generation_prompt(json.loads(description),cfg,module,None) or body in prompt or (wrap and wrap in prompt):
            raise ValueError('Reference/wrapper module leaked into prompt')
        rendered=tokenizer.apply_chat_template([dict(role='user',content=prompt)],tokenize=False,add_generation_prompt=True)
        tokens=tokenizer(rendered,add_special_tokens=False,truncation=False)['input_ids']
        if not tokens or tokens[0]!=tokenizer.bos_token_id or tokens.count(tokenizer.bos_token_id)!=1:
            raise ValueError('Exact single-BOS Llama chat input required')
        dependencies=dependency_closure(body,module,m2p)
        wrapper_dependencies=dependency_closure(wrap,runner.module_name(wrap),m2p) if wrap else {}
        # The candidate itself is never copied back as a hidden dependency.
        wrapper_dependencies={p:h for p,h in wrapper_dependencies.items() if runner.module_name(Path(p).read_text())!=module}
        rows.append(dict(id=num,spec=num,module_name=module,population=population(num),split='official_holdout30',
            prompt=prompt,prompt_sha256=sha(prompt.encode()),description=dict(metadata(desc),bytes=description),
            config=dict(metadata(path),bytes=cfg,label=label),source=metadata(src),dependencies=dependencies,
            wrapper=metadata(wp) if wp else None,wrapper_dependencies=wrapper_dependencies,
            rendered_prompt=rendered,rendered_prompt_sha256=sha(rendered.encode()),input_token_ids=tokens,
            input_token_ids_sha256=digest(tokens),input_tokens=len(tokens),required_context=len(tokens)+16384))
    return rows


def validate_export(packet):
    environment()
    if (not isinstance(packet,dict) or set(packet)!=PACKET_FIELDS or
        any(packet.get(k)!=v or type(packet.get(k)) is not type(v) for k,v in CONTRACT.items())):
        raise ValueError('Exact evaluation-only fullmodule30 diagnostic contract required')
    rows=packet.get('tasks')
    if (not isinstance(rows,list) or [r['id'] for r in rows]!=list(IDS) or digest(rows)!=ROWS_SHA or
        packet.get('holdout_sha256')!=HOLDOUT_SHA or packet.get('prompt_environment')!=PROMPT_ENV or
        digest(packet.get('inventories'))!=INPUTS_SHA):raise ValueError('Frozen exact population/input/encoding inventory changed')
    if packet.get('population_counts')!=COUNTS:raise ValueError('Protected population composition changed')
    if (packet['source_sha256']!=sources() or packet['cpu_environment']!=CPU_ENV or
        packet['prerequisites']!=PREREQUISITES or packet['data_role']!=DATA_ROLE or
        packet['g1_missing_source_ids']!=['120'] or packet['g1_source_inventory_count']!=205):
        raise ValueError('Source/admission/data-protection prerequisites changed')
    for row in rows:
        desc=row['description'];cfg=row['config']
        prompt=framing.build_generation_prompt(json.loads(desc['bytes']),cfg['bytes'],row['module_name'],None)
        if prompt!=row['prompt'] or sha(prompt.encode())!=row['prompt_sha256']:
            raise ValueError('Exact description/config-only Framing-A prompt required')
        if sha(desc['bytes'].encode())!=desc['sha256'] or sha(cfg['bytes'].encode())!=cfg['sha256']:
            raise ValueError('Exact description/config bytes required')
        if row['required_context']!=row['input_tokens']+16384:raise ValueError('Full official output ceiling required')
    if packet.get('minimum_required_context')!=max(r['required_context'] for r in rows):raise ValueError('No context truncation or hidden overflow')
    return rows


validate_packet=validate_export


def build():
    from transformers import AutoTokenizer
    environment();before=inventories();source_before=sources()
    if digest(before)!=INPUTS_SHA:raise ValueError('Frozen source/config/tokenizer inputs changed')
    tokenizer=AutoTokenizer.from_pretrained(TOKENIZER,local_files_only=True)
    rows=make_rows(tokenizer)
    packet=dict(CONTRACT,holdout_sha256=HOLDOUT_SHA,prompt_environment=environment(),cpu_environment=CPU_ENV,
        population_counts=COUNTS,tasks=rows,inventories=before,source_sha256=source_before,
        minimum_required_context=max(r['required_context'] for r in rows),
        prerequisites=PREREQUISITES,data_role=DATA_ROLE,
        g1_missing_source_ids=['120'],g1_source_inventory_count=205)
    validate_export(packet)
    if before!=inventories() or source_before!=sources():raise ValueError('Input/source drift during packet preparation')
    return packet


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();packet=build();args.output.mkdir(parents=True,exist_ok=False)
    with (args.output/'prompts.json').open('x') as f:json.dump(packet,f,indent=2);f.write('\n')
    print(json.dumps(dict(tasks=30,requested_samples=60,minimum_required_context=packet['minimum_required_context'],
        packet_sha256=file_sha(args.output/'prompts.json'),launch_authorized=False,oracle_controls_performed=False)))


if __name__=='__main__':main()
