"""Two full-context TRAIN repair diagnostics; no generation, training or gate claim."""
import argparse
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_sumsequence_proof_rl_verify as verified
from tools.proof_cuda_train import file_sha,dump
from tools.proof_cuda_eval import digest,sha

checks=verified.checks;policy=verified.evaluation
RUNS=ROOT/'results/runs'
VERIFIED=RUNS/'proof-sumsequence-proof-rl-verified-20260906-v1'
GENERATIONS=RUNS/'proof-sumsequence-proof-rl-eval-20260906-v1'
BASELINE=RUNS/'proof-sumsequence-repair-cycle-20260906-v1/child'
PROMPTS=RUNS/'proof-sumsequence-repair-packet-20260906-main-v2/prompts.json'
TOKENIZER=RUNS/'proof-cuda-tokenizer-20260905-v2'
CONTROLS=RUNS/'proof-sumsequence-proof-rl-checks-20260906-v1'
POLICY_SHA='1bb603f605ddc0307631b0db4bda3fdfa109b5e0493f4508db05334deff87ee2'
PINS={VERIFIED/'rows.json':'bf5617d90da381ea1865d7b123da33dec9a9973355038e8ca738bed64bc2a1cb',
      VERIFIED/'summary.json':'9278f5141b60a1a03790b0299618b728bde0f42bab020c6112ea2bb388182b7a',
      GENERATIONS/'accounting.json':'56a373407a4150cfbaebe5a5ccc9957bee0fa9c569173794c8190eb589f14b59'}
IDS=('breadth-ReachabilityProofs-Reachable1','sumsequence-Lemma3')
BUDGET=dict(original_denominator=40,diagnostic_tasks=2,attempts_per_task=1,max_context=8192,
    max_new_tokens=3072,maximum_input_tokens=5120,truncation=False,inference_only=True,
    generation_performed=False,optimizer_updates=0,repair_budget_authorized=False)
SOURCES=tuple(sorted(set(verified.SOURCES)|{'tools/proof_sumsequence_sany_repair_packet.py'}))


def load(path):return json.loads(Path(path).read_bytes())


def sources():return {name:file_sha(ROOT/name) for name in SOURCES}


def checked(path,expected):
    if file_sha(path)!=expected:raise ValueError('Immutable input changed: '+str(path))


def exclusion_bindings(tasks):
    broader=policy.greedy.broader;extra=policy.greedy.extra
    manifests=broader.load_manifests();broader.reconstruct(manifests)
    extra.audit_exclusions()
    return dict(original_manifest_sha256=broader.SOURCE_MANIFEST_SHA256,
        original_exclusion_sha256=digest(manifests['original6']['exclusion_sha256']),
        original_task_decontamination={t['id']:t['decontamination'] for t in tasks if t['id']==IDS[0]},
        sumsequence_reports={run:pin for run,pin in extra.REPORTS.items()},
        protected_populations=['official119','official30','original18','development'],
        audit='Existing exact source/goal exclusions reconstructed; no protected answers exported',
        clean_generalization_claim=False)


def admit():
    for path,pin in PINS.items():checked(path,pin)
    checked(PROMPTS,policy.PROMPTS_SHA)
    before=load(VERIFIED/'identity_before.json')
    if before!=load(VERIFIED/'identity_after.json'):raise ValueError('Completed replay identity was unstable')
    for path,pin in before['files'].items():checked(Path(path),pin)
    if before['sources']!={name:file_sha(ROOT/name) for name in verified.SOURCES}:
        raise ValueError('Historical verified source identity changed')
    tasks=checks.admit_tasks(load(PROMPTS));current=checks.admit_controls(CONTROLS,tasks)
    if current!=before['verifier']:raise ValueError('Current actual checker identity changed')
    exclusion=exclusion_bindings(tasks)
    records=load(VERIFIED/'rows.json');arms=dict(parent=load(BASELINE/'accounting.json'),child=load(GENERATIONS/'accounting.json'))
    verified.audit_rows(tasks,arms,records,current,VERIFIED)
    summary=load(VERIFIED/'summary.json')
    expected=verified.summarize(records,tasks,True)
    if (summary.get('complete') is not True or summary.get('identity_stable') is not True or
        any(summary.get(k)!=v for k,v in expected.items())):raise ValueError('Actual complete80 summary differs from raw evidence')
    admission=load(GENERATIONS/'admission.json')
    if admission['checkpoint_sha256']!=POLICY_SHA or summary['training_linkage']['child_sha256']!=POLICY_SHA:
        raise ValueError('Exact actual one-update child policy required')
    import transformers
    tokenizer=transformers.AutoTokenizer.from_pretrained(TOKENIZER,local_files_only=True)
    expected_files={n:h for n,h in admission['model_files'].items() if n.endswith('.json') or n in ('tokenizer.model','chat_template.jinja')}
    actual={p.name:file_sha(p) for p in TOKENIZER.iterdir() if p.is_file() and (p.suffix=='.json' or p.name in ('tokenizer.model','chat_template.jinja'))}
    if expected_files!=actual:raise ValueError('Complete exact original tokenizer required')
    portable=policy.greedy.validate_export(load(PROMPTS))
    if [policy.common.encode_prompt(tokenizer,t) for t in portable]!=admission['encodings']:
        raise ValueError('Original40 exact prompt/input tokens changed')
    policy.validate_rows(admission,arms['child'],tokenizer)
    return tasks,portable,arms['child'],records[40:],tokenizer,dict(
        verified_rows_sha256=PINS[VERIFIED/'rows.json'],verified_summary_sha256=PINS[VERIFIED/'summary.json'],
        generation_rows_sha256=PINS[GENERATIONS/'accounting.json'],
        original_prompt_packet_sha256=policy.PROMPTS_SHA,tokenizer_files=actual,
        original_identity_sha256=digest(before),exclusion=exclusion)


def feedback(raw,record):
    if record['raw_row_sha256']!=digest(raw) or record['finish_reason']!=raw['finish_reason']:
        raise ValueError('Exact original failed response/verification linkage required')
    if raw['id']==IDS[0]:
        if (raw['finish_reason']!='token_limit' or len(raw['token_ids'])!=3072 or
            record['sany'] is not None or record['proof'] is not None or record['evidence'] is not None):
            raise ValueError('Original Reachable1 cap is unmeasured, not a SANY failure')
        return dict(kind='generation_cap',sany_diagnostic=None,sany_attempted=False,
            text='The previous response exhausted the3072-token output budget without EOS. It was not checked by SANY. Produce a complete replacement proof within3072 output tokens; do not continue or truncate the previous response.')
    if raw['id']!=IDS[1] or raw['finish_reason']!='eos' or record['sany']!=0 or record['status']!='model_sany_reject':
        raise ValueError('Original complete Lemma3 SANY rejection required')
    sany=record['evidence']['evidence']['sany_evidence']
    if sany['status']!='model_sany_reject' or sany['reward']!=0 or not sany['output']:
        raise ValueError('Actual raw SANY diagnostic required')
    return dict(kind='sany_rejection',sany_diagnostic=sany['output'],sany_attempted=True,
        sany_record_sha256=digest(sany),text='The previous complete response was rejected by SANY. The complete raw checker output follows:\n'+sany['output'])


def prompt(original,raw,diagnostic):
    # Only the already-exported original prompt, actual model reply and raw
    # diagnostic may supply text. Task reference fragments never enter here.
    return (original['prompt']+'\n\nREPAIR DIAGNOSTIC (supporting attempt; original theorem and module context remain immutable)\n'
        'Previous raw model response, verbatim:\n<previous_response>\n'+raw['raw_reply']+'\n</previous_response>\n\n'
        +diagnostic['text']+'\n\nReturn only one complete replacement proof fragment under the original output contract. '
        'Do not change the theorem, assumptions, definitions, dependencies or module context. Do not introduce axioms, OMITTED or an assumed copy of the target.\n')


def build(tasks,portable,raw_rows,records,tokenizer,provenance):
    if len(tasks)!=40 or len(portable)!=40 or len(raw_rows)!=40 or len(records)!=40:
        raise ValueError('Preserve original40 task denominator and complete child evidence')
    expected=[t['id'] for t in tasks]
    if any([r['id'] for r in group]!=expected for group in (portable,raw_rows,records)):
        raise ValueError('Exact ordered40 source/input/result binding required')
    misses=[r['id'] for r in records if r['sany']!=1]
    if misses!=list(IDS):raise ValueError('Exactly the two actual first-milestone misses required')
    rows=[]
    for index,(task,original,raw,record) in enumerate(zip(tasks,portable,raw_rows,records)):
        if task['id'] not in IDS:continue
        if task['split']!='train' or original['split']!='train':raise ValueError('No development/holdout repair inputs allowed')
        if original['prompt_sha256']!=sha(original['prompt'].encode()) or raw['raw_reply_sha256']!=sha(raw['raw_reply'].encode()):
            raise ValueError('Exact original prompt and failed raw reply hashes required')
        checked(Path(task['source_path']),task['source_sha256'])
        if set(task['dependencies'])!=set(task['dependency_sha256']):raise ValueError('Complete immutable dependency inventory required')
        for path,pin in task['dependency_sha256'].items():checked(Path(path),pin)
        if task['prefix'] not in original['prompt'] or task['suffix'] not in original['prompt']:
            raise ValueError('Complete immutable original module prefix/suffix required')
        diagnostic=feedback(raw,record);text=prompt(original,raw,diagnostic)
        exported=dict(id=task['id'],split='train',prompt=text,prompt_sha256=sha(text.encode()))
        encoded=policy.common.encode_prompt(tokenizer,exported)
        total=encoded['input_tokens']+3072;overage=max(0,total-8192)
        rows.append(dict(**exported,original_index=index,original_prompt=original['prompt'],
            original_prompt_sha256=original['prompt_sha256'],raw_failed_reply=raw['raw_reply'],
            raw_failed_reply_sha256=raw['raw_reply_sha256'],raw_row_sha256=digest(raw),
            verification_row_sha256=digest(record),failure=diagnostic,
            context=dict(prefix=task['prefix'],suffix=task['suffix'],theorem_name=task['theorem_name'],
                source_path=task['source_path'],source_sha256=task['source_sha256'],source_commit=task['source_commit'],
                source_family=task['source_family'],dependencies=task['dependencies'],dependency_sha256=task['dependency_sha256']),
            encoding=encoded,input_tokens=encoded['input_tokens'],output_budget=3072,total_context_tokens=total,
            context_overage_tokens=overage,executable_full_context=overage==0,reference_answer_exported=False))
    return dict(schema=1,kind='two_train_first_milestone_repair_diagnostics',policy_sha256=POLICY_SHA,
        budget=BUDGET,original_requested_ids=expected,original_denominator=40,diagnostic_tasks=2,
        tasks=rows,executable_tasks=sum(r['executable_full_context'] for r in rows),
        provenance=provenance,reference_answers_exported=False,generalization_claim=False,gate_claim=False,
        pass_at1_claim=False,source_sha256=sources(),
        scope='Two selected TRAIN repair attempts; never pooled into original greedy40 or a new milestone claim. Context overflows are reported, never truncated.')


def validate_packet(packet,*values):
    if packet!=build(*values):raise ValueError('Exact full repair prompt/evidence/token/context contract required')


def create(output):
    output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    dump(output/'summary.json',dict(complete=False,original_denominator=40,diagnostic_tasks=2,generation_performed=False))
    try:
        before=sources();values=admit();packet=build(*values);validate_packet(packet,*values)
        # Recheck immutable source/verification inputs after encoding, without
        # rerunning any candidate or creating a new verifier outcome.
        for path,pin in PINS.items():checked(path,pin)
        identity=load(VERIFIED/'identity_before.json')
        for path,pin in identity['files'].items():checked(Path(path),pin)
        if sources()!=before or packet['source_sha256']!=before:raise ValueError('Packet source changed during creation')
        dump(output/'packet.json',packet)
        summary=dict(complete=True,packet_sha256=file_sha(output/'packet.json'),original_denominator=40,diagnostic_tasks=2,
            executable_tasks=packet['executable_tasks'],generation_performed=False,optimizer_updates=0,
            tasks=[{k:r[k] for k in ('id','input_tokens','output_budget','total_context_tokens','context_overage_tokens','executable_full_context')} for r in packet['tasks']])
        dump(output/'summary.json',summary);return summary
    except BaseException as exc:
        dump(output/'failure.json',dict(error=type(exc).__name__+': '+str(exc)));raise


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True)
    print(json.dumps(create(p.parse_args().output)))


if __name__=='__main__':main()
