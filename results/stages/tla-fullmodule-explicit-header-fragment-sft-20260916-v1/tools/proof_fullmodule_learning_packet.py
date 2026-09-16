"""Mixed TRAIN169 syntax-supervision data; retained42 plus admitted W4 syntax127.

New whole-module targets are parser-verified, not semantic/proof certificates.
Preparation never authorizes an optimizer or use of protected evaluation data.
"""
import argparse
import json
from pathlib import Path
import sys
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_sany_repair_learning_packet as retained
from tools import proof_fullmodule_training_checks as controls

audit=controls.preparation;load=audit.load;sha=retained.sha;digest=retained.digest;file_sha=retained.file_sha;dump=retained.dump
RUNS=ROOT/'results/runs'
OLD=RUNS/'proof-sany-repair-learning-packet-20260906-v1/train.json'
OLD_SHA='d370761500e0f828f536d74fffd7d9785df34215ffa61c09490bccbcfe6544d7'
AUDIT=controls.AUDIT_ROOT
CONTROLS=RUNS/'proof-fullmodule-training-checks-20260906-v1'
CONTROL_PINS={'rows.json':'9171e888ff467ccac4dfa2ee70e022b4e6ec3f5ad07f2d7e1391e5187a2686e4',
    'summary.json':'90b81f26c9cc2d1ad6c37b30e0b19eedf5bac9394e1d1f1041c5a3f290915de2',
    'process.json':'5dc7335501d2aba8f464e18b194a39e0b4b25ed8bceb632feb1e17c920866801',
    'receipt.json':'6dc2243cc77199f3d147851e6d1f72db7dc8246ddc76a3c69f3a569d3052d248',
    'config.json':'d1600615665188609d172583f888fb7f20972455619c3a3cc28e1881bf5d1d99',
    'tasks.json':'568192acf1ce24a6eeef1d4c0c9a842da521584f7595a15a2439ad30d15b4bb8',
    'identity_before.json':'df1159cb5550c2ce4588d43b8aba63ef5bfdddefa7f0590b1b1b4f56edb5b90a',
    'identity_after.json':'df1159cb5550c2ce4588d43b8aba63ef5bfdddefa7f0590b1b1b4f56edb5b90a'}
PARENT_SHA='88660d5a17eab6ae23adf109e5619db0feb986254e8b46460899a528781cdde3'
BLOCKED='w4opus::d4-m9-p4-t2'
SOURCES=tuple(sorted(set(retained.SOURCES)|set(controls.SOURCES)|{'tools/proof_fullmodule_learning_packet.py'}))
CONTRACT=dict(schema=1,packet_kind='mixed_retained42_fullmodule_syntax127',algorithm='response-only supervised mixed proof retention and full-module syntax',
    split='train',requested_rows=169,retained_rows=42,new_fullmodule_rows=127,audited_candidates=128,
    excluded_candidates=1,parent_checkpoint_sha256=PARENT_SHA,max_tokens=9216,truncation=False,
    training_authorized=False,model_training_performed=False,on_policy_rewards=False,
    new_data_syntax_only=True,new_data_semantic_admission=False,proof_claim=False,nonvacuity_claim=False,
    generalization_claim=False,gate_claim=False,protected_failure_feedback_used=False,
    parent_checkpoint_validation_required=True)
TOP_FIELDS=set(CONTRACT)|{'old_packet_bytes','audit_rows_bytes','control_rows_bytes','controls_summary_bytes',
    'controls_receipt_bytes','rows','encodings','eligibility','rows_sha256','encodings_sha256','eos_token_id',
    'audit_pins','control_pins','source_sha256','protected_evidence_sha256','identity','max_full_tokens'}


def exact(text,pin):
    if not isinstance(text,str) or sha(text.encode())!=pin:raise ValueError('Exact immutable original bytes required')
    return json.loads(text)


def sources():return {n:file_sha(ROOT/n) for n in SOURCES}


def expected_files():
    return {str(OLD.relative_to(ROOT)):OLD_SHA,**{str((AUDIT/n).relative_to(ROOT)):h for n,h in controls.PINS.items()},
        **{str((CONTROLS/n).relative_to(ROOT)):h for n,h in CONTROL_PINS.items()}}


def compose(old_bytes,audit_bytes,control_bytes):
    old=exact(old_bytes,OLD_SHA);old_rows=retained.validate_training_packet(old)
    candidates=exact(audit_bytes,controls.PINS['rows.json']);checked=exact(control_bytes,CONTROL_PINS['rows.json'])
    if len(candidates)!=128 or [r['index'] for r in candidates]!=audit.indices() or len(checked)!=256:
        raise ValueError('Complete original128 selection and256 fresh controls required')
    rows=list(old_rows);encodings=list(old['encodings']);eligibility=[]
    for order,candidate in enumerate(candidates):
        raw=candidate['raw'];reply=raw['spec_text'];positive,negative=checked[2*order:2*order+2]
        for row,label,value in [(positive,'reference',reply),(negative,'syntax_negative',controls.common.negative(reply))]:
            result=row['result']
            if (row['id']!=candidate['id'] or row['index']!=candidate['index'] or row['label']!=label or row['accepted'] is not True or
                result['raw_reply_sha256']!=sha(value.encode()) or result['module']!=controls.common.gen_eval.extract_module(value)):
                raise ValueError('Exact current control-to-candidate linkage required')
            if result['process'] is None or not all(result['process'].get(k) is True for k in ('execution_complete','cleanup_complete','output_complete')):
                raise ValueError('Incomplete control process cannot admit data')
        if positive['result']['sany']!=1 or not controls.negative_accepted({},controls.common.negative(reply),negative['result']):
            raise ValueError('Actual target positive and intended parser-negative required')
        clear=candidate['exclusions']['status']=='lexically_clear'
        if (not clear)!=(candidate['id']==BLOCKED) or candidate['raw_sha256']!=digest(raw):
            raise ValueError('Original unresolved-invariant exclusion must remain blocked')
        disposition=dict(id=candidate['id'],index=candidate['index'],included=clear,
            reason='lexically_clear_and_fresh_sany' if clear else 'blocked_unresolved_invariant',
            audit_row_sha256=digest(candidate),positive_control_sha256=digest(positive),negative_control_sha256=digest(negative),
            new_data_semantic_admission=False)
        eligibility.append(disposition)
        if not clear:continue
        e=candidate['encoded'];identifier='w4-fullmodule:'+candidate['id']
        if e['response']!=reply or e['response_sha256']!=sha(reply.encode()):raise ValueError('Exact source module only target required')
        row=dict(id=identifier,split='train',source_family='W4:synthetic_fullmodule',source_sha256=sha(reply.encode()),
            assembled_sha256=sha(reply.encode()),prompt=e['prompt'],prompt_sha256=e['prompt_sha256'],
            response=reply,response_sha256=sha(reply.encode()))
        rows.append(row);encodings.append(dict(e['encoding'],id=identifier,prompt_sha256=row['prompt_sha256'],response_sha256=row['response_sha256']))
    if len(rows)!=169 or len({r['id'] for r in rows})!=169 or sum(r['included'] for r in eligibility)!=127:
        raise ValueError('Exact retained42 plus127 syntax targets required')
    return rows,encodings,eligibility,old['eos_token_id']


def validate_training_packet(value):
    if (not isinstance(value,dict) or set(value)!=TOP_FIELDS or
        any(value.get(k)!=v or type(value.get(k)) is not type(v) for k,v in CONTRACT.items())):
        raise ValueError('Exact mixed169 syntax-only, no-training-authorization contract required')
    rows,encodings,eligibility,eos=compose(value['old_packet_bytes'],value['audit_rows_bytes'],value['control_rows_bytes'])
    if (value['rows']!=rows or value['encodings']!=encodings or value['eligibility']!=eligibility or value['eos_token_id']!=eos or
        value['rows_sha256']!=digest(rows) or value['encodings_sha256']!=digest(encodings)):
        raise ValueError('Original rows, encoding masks or all128 dispositions changed')
    summary=exact(value['controls_summary_bytes'],CONTROL_PINS['summary.json']);receipt=exact(value['controls_receipt_bytes'],CONTROL_PINS['receipt.json'])
    if (summary['complete'] is not True or summary['target_sany_pass']!=128 or summary['intended_negative_controls']!=128 or
        summary['unknown_controls']!=0 or summary['blocked_candidate_ids']!=[BLOCKED] or receipt['complete'] is not True or
        receipt['process_sha256']!=CONTROL_PINS['process.json'] or receipt['summary_sha256']!=CONTROL_PINS['summary.json']):
        raise ValueError('Complete authenticated256-control receipt required')
    if (value['audit_pins']!=controls.PINS or value['control_pins']!=CONTROL_PINS or
        value['protected_evidence_sha256']!=controls.PINS['protected_evidence.json']):
        raise ValueError('Frozen protected exclusion and control inventories required')
    if value['source_sha256']!=sources() or value['identity']!=dict(files=expected_files(),sources=value['source_sha256']):
        raise ValueError('Exact current source and pinned input identities required')
    for row,e in zip(rows,encodings):
        if set(row)!=retained.original.ROW_FIELDS:raise ValueError('Unchanged nine model-ready fields required')
        ids=e['input_ids'];n=e['prompt_tokens']
        if (type(n) is not int or not 0<n<len(ids)<=9216 or ids[-1]!=eos or e['labels']!=[-100]*n+ids[n:] or
            e['response_tokens']!=len(ids)-n or any(type(t) is not int or t<0 for t in ids)):
            raise ValueError('Complete exact prefix/response-only/EOS encoding required')
    if value['max_full_tokens']!=max(len(e['input_ids']) for e in encodings):raise ValueError('Full context accounting changed')
    return rows


validate_export=validate_training_packet


def identity():
    files={str(OLD.relative_to(ROOT)):file_sha(OLD)}
    for root,pins in [(AUDIT,controls.PINS),(CONTROLS,CONTROL_PINS)]:
        for name in pins:files[str((root/name).relative_to(ROOT))]=file_sha(root/name)
    return dict(files=files,sources=sources())


def payload():
    """Pure artifact composition; does not certify current runtime or write output."""
    old=OLD.read_text();candidate=(AUDIT/'rows.json').read_text();checked=(CONTROLS/'rows.json').read_text()
    rows,encodings,eligibility,eos=compose(old,candidate,checked)
    return dict(CONTRACT,old_packet_bytes=old,audit_rows_bytes=candidate,control_rows_bytes=checked,
        controls_summary_bytes=(CONTROLS/'summary.json').read_text(),controls_receipt_bytes=(CONTROLS/'receipt.json').read_text(),
        rows=rows,encodings=encodings,eligibility=eligibility,eos_token_id=eos,
        rows_sha256=digest(rows),encodings_sha256=digest(encodings),audit_pins=controls.PINS,control_pins=CONTROL_PINS,
        source_sha256=sources(),protected_evidence_sha256=controls.PINS['protected_evidence.json'],identity=identity(),
        max_full_tokens=max(len(e['input_ids']) for e in encodings))


def admit():
    before=identity()
    for root,pins in [(AUDIT,controls.PINS),(CONTROLS,CONTROL_PINS)]:
        for name,pin in pins.items():controls.common.checked(root/name,pin)
    controls.common.checked(OLD,OLD_SHA)
    controls.audit(SimpleNamespace(audit_root=AUDIT,output=CONTROLS))  # Current raw owned SANY replay; no new checks.
    value=payload();validate_training_packet(value)
    from transformers import AutoTokenizer
    tokenizer=AutoTokenizer.from_pretrained(audit.framing.TOKENIZER,local_files_only=True)
    for row,e in zip(value['rows'],value['encodings']):
        actual=retained.encode_candidate(tokenizer,row['prompt'],row['response'],9216)
        expected=dict(actual,id=row['id'],prompt_sha256=row['prompt_sha256'],response_sha256=row['response_sha256'])
        if expected!=e:raise ValueError('Complete actual169 local-tokenizer reconstruction differs')
    if before!=identity() or value['identity']!=before:raise ValueError('Source/artifact drift during packet admission')
    return value


def build(output):
    output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    dump(output/'summary.json',dict(complete=False,requested_rows=169,admitted_rows=0,training_authorized=False))
    value=admit();dump(output/'train.json',value)
    summary=dict(complete=True,requested_rows=169,retained_rows=42,new_syntax_rows=127,audited_candidates=128,
        excluded_ids=[BLOCKED],max_full_tokens=value['max_full_tokens'],train_sha256=file_sha(output/'train.json'),
        rows_sha256=value['rows_sha256'],encodings_sha256=value['encodings_sha256'],
        parent_checkpoint_sha256=PARENT_SHA,training_authorized=False,new_data_semantic_admission=False)
    dump(output/'summary.json',summary);return summary


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    try:print(json.dumps(build(a.output)))
    except BaseException as exc:
        if a.output.is_dir():dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc),training_authorized=False))
        raise


if __name__=='__main__':main()
