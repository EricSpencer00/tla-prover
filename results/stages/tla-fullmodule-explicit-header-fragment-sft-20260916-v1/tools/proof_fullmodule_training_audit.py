"""Source-ordered W4 TRAIN candidate audit only: no checker/model/training run."""
import argparse
import json
import os
from pathlib import Path
import re
import sys

CPU_ENV={n:'4' for n in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS')}
os.environ.update(CPU_ENV,HF_HUB_OFFLINE='1',TRANSFORMERS_OFFLINE='1',TOKENIZERS_PARALLELISM='false')
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from harness import w4_corpus,gen_eval,runner
from harness.repair import extract_definitions
from tools import proof_breadth_manifest as exclusion
from tools import proof_fullmodule_holdout_packet as framing
from tools.proof_candidate_rank import encode_candidate
from tools.proof_cuda_eval import digest,sha,dump
from tools.proof_cuda_train import file_sha

RUNS=ROOT/'results/runs';EXCLUSIONS=ROOT/'results/analysis/w4_exclusions.json'
MANIFEST=RUNS/'proof-breadth-controls-20260905-v1/manifest.json'
MANIFEST_SHA='23d15fba5fcb08e8d8436d02deb727a34976bc220e8d66ec7bc333728949627e'
EXCLUSIONS_SHA='9423ebb427ddf654d0b27806daac9c8952cf8550d77fc3a5bc58248d71e2ca68'
INPUTS_SHA='4b76d9f3edea363c01ac4909784bf03b1ea2ca8d95b5384a4d5cf33c9c3856fd'
EFFECTIVE_SHA='af186cbc0b33fb9477a32566078346e520b109fb9d46d932ed529044953a9b4e'
COUNT=128;TOTAL=5010;THRESHOLD=.65
SOURCES=tuple(sorted(set(framing.SOURCES)|{
    'harness/w4_corpus.py','harness/corpora.py','tools/proof_breadth_manifest.py',
    'tools/proof_source_scope.py','tools/proof_candidate_rank.py','tools/proof_cuda_eval.py',
    'tools/proof_cuda_train.py','tools/proof_original18.py','tools/proof_fullmodule_training_audit.py',
    'harness/proof_fragment_check.py','harness/proof_full_fragment_check.py','tools/proof_dev_manifest.py',
    'tools/proof_family_manifest.py','tools/proof_premise_search.py','tools/proof_fact_search.py',
    'tools/proof_official_extension.py','tools/proof_repair_pilot.py','tools/proof_sequence_train.py'}))


def load(path):return json.loads(Path(path).read_bytes())
def pin(path,h):
    if file_sha(path)!=h:raise ValueError('Immutable input changed: '+str(path))


def indices(total=TOTAL,count=COUNT):
    if type(total) is not int or type(count) is not int or not 1<count<=total:
        raise ValueError('Integer population and at least two evenly spaced selections required')
    result=[i*(total-1)//(count-1) for i in range(count)]
    if len(set(result))!=count or result[0]!=0 or result[-1]!=total-1:raise ValueError('Exact evenly spaced endpoints required')
    return result


def inventory():
    files=[EXCLUSIONS,MANIFEST,ROOT/'corpus/holdout_30.json',ROOT/'corpus/lmgpa/manifest.json']
    files+=sorted(RUNS.glob('w4-opus-shard*/w2_survivors.jsonl'))
    files += sorted(p for p in framing.TOKENIZER.iterdir() if p.is_file() and (p.suffix=='.json' or p.name in ('tokenizer.model','chat_template.jinja')))
    return {str(p.resolve()):file_sha(p) for p in files}


def source_identity():return {n:file_sha(ROOT/n) for n in SOURCES}


def candidates():
    pin(EXCLUSIONS,EXCLUSIONS_SHA)
    rows=w4_corpus.load_effective(runs_dir=RUNS,exclusions=load(EXCLUSIONS))
    if len(rows)!=TOTAL or len({r['seed_key'] for r in rows})!=TOTAL or digest(rows)!=EFFECTIVE_SHA:
        raise ValueError('Complete frozen5010 source-ordered effective population required')
    selected=[]
    for index in indices():
        row=rows[index];path=RUNS/f"w4-opus-shard{row['_shard']}/w2_survivors.jsonl"
        matches=[]
        for line,raw in enumerate(path.read_text().splitlines(),1):
            if raw.strip() and dict(json.loads(raw),_shard=row['_shard'])==row:matches.append(line)
        if not matches:raise ValueError('Selected effective row not present in pinned source ledger')
        selected.append(dict(index=index,id=row['seed_key'],raw=row,raw_sha256=digest(row),
            source_ledger=str(path),source_ledger_sha256=file_sha(path),matching_source_lines=matches))
    return selected


def protected():
    pin(MANIFEST,MANIFEST_SHA);parent=load(MANIFEST)
    for name,count in [('official119',119),('official30',30)]:
        ids=[r['id'] for r in parent['official_sources'] if r['id'].startswith(name+':')]
        if len(ids)!=count or len(set(ids))!=count:raise ValueError('Complete protected population required')
    if file_sha(ROOT/'corpus/holdout_30.json')!=framing.HOLDOUT_SHA:raise ValueError('Protected holdout membership changed')
    sources,goals,provenance,dev=exclusion.exclusions(parent)
    if provenance!=parent['exclusion_sha256']:raise ValueError('Actual complete protected source/archived reference identity changed')
    if len([n for n,_ in sources if n.startswith('original18:')])!=18 or len([n for n,_ in sources if n.startswith('original18-reference:')])!=18:
        raise ValueError('Complete recovered original18 prompt/reference exclusion required')
    # Preserve the established raw-source pools, and additionally cover the
    # patched/wrapper context used by current full-module evaluation.
    holdout_inputs=framing.inventories()
    if digest(holdout_inputs)!=framing.INPUTS_SHA:raise ValueError('Current protected canonical/patch/wrapper inventory changed')
    n2m,m2p=runner.build_module_index(framing.CORPUS)
    for num in framing.IDS:
        path=framing.source_path(num);body=path.read_text()
        sources.append(('official30-canonical:'+num,body))
        for dep,h in framing.dependency_closure(body,n2m[num],m2p).items():
            pin(dep,h);sources.append(('official30-dependency:'+num+':'+dep,Path(dep).read_text()))
        wrapper=framing.wrapper_path(num,n2m,m2p)
        if wrapper:
            body=wrapper.read_text();sources.append(('official30-wrapper:'+num,body))
            for dep,h in framing.dependency_closure(body,runner.module_name(body),m2p).items():
                pin(dep,h);sources.append(('official30-wrapper-dependency:'+num+':'+dep,Path(dep).read_text()))
    # Add operator bodies to the goal pool: full-module targets often contain no
    # named theorem. This conservative lexical audit is not semantic equivalence.
    operators=[]
    for ident,text in sources:
        for name,body in extract_definitions(exclusion.top_level_code(text)).items():
            operators.append((ident+':operator:'+name,body.split('==',1)[1].strip()))
    goals=goals+operators+[(n+':'+name,body) for n,text in sources if n.startswith('official30-') for name,body in exclusion.goal_bodies(text)]
    if not sources or not goals:raise ValueError('Nonempty protected source and goal pools required')
    evidence=dict(manifest_sha256=MANIFEST_SHA,provenance=provenance,
        manifests={str(ROOT/'corpus/holdout_30.json'):file_sha(ROOT/'corpus/holdout_30.json'),
                   str(ROOT/'corpus/lmgpa/manifest.json'):file_sha(ROOT/'corpus/lmgpa/manifest.json')},
        population_counts=dict(official30=30,official119=119,original18=18,development=len(dev)),
        protected_current_holdout_inputs_sha256=digest(holdout_inputs),
        source_sha256={n:sha(s.encode()) for n,s in sources},goal_sha256={n:sha(s.encode()) for n,s in goals},
        threshold=THRESHOLD,reference_answers_exported=False,
        method='Existing normalized source and scope-aware theorem comparisons plus conservative top-level operator-body comparisons',
        limitation='Lexical exclusions only; operator extraction is heuristic; unknown pretraining not certified')
    return sources,goals,evidence


def pool(rows):return [(name,*exclusion.comparison_key(text)) for name,text in rows]


def compare(text,prepared):
    if not prepared:raise ValueError('Empty protected pool is not clear')
    tokens,h=exclusion.comparison_key(text)
    score,name=max((exclusion.jaccard(tokens,other),name) for name,other,_ in prepared)
    return dict(max_jaccard=score,nearest=name,exact_normalized=[name for name,_,other in prepared if other==h])


def exclusion_audit(row,sources,goals):
    text=row['spec_text'];named=exclusion.goal_bodies(text)
    blocks=extract_definitions(exclusion.top_level_code(text));pi=row.get('property_invariant')
    unresolved=not isinstance(pi,str) or pi not in blocks
    if not unresolved:named.append(('declared_invariant:'+pi,blocks[pi].split('==',1)[1].strip()))
    checks={'full_module':compare(text,sources),'description':compare(row['nl'],sources),
        **{'goal:'+str(i)+':'+name:compare(body,goals) for i,(name,body) in enumerate(named)}}
    overlap=any(v['max_jaccard']>=THRESHOLD or v['exact_normalized'] for v in checks.values())
    return dict(status='excluded_lexical_overlap' if overlap else 'unknown_invariant_goal' if unresolved else 'lexically_clear',
        checks=checks,declared_invariant=pi,invariant_resolved=not unresolved,named_goal_count=len(named),
        historical_decontamination_not_trusted=True,threshold=THRESHOLD)


def encode(row,tokenizer):
    framing.environment()
    for k in ('nl','spec_text','cfg_text','module'):
        if not isinstance(row.get(k),str) or not row[k]:raise ValueError('Complete explicit NL/module/config/target required')
    if runner.module_name(row['spec_text'])!=row['module']:raise ValueError('Raw target module name mismatch')
    description={'system_overview':row['nl']}
    prompt=gen_eval.build_generation_prompt(description,row['cfg_text'],row['module'],None)
    if row['spec_text'] in prompt:raise ValueError('Reference module leaked into user prompt')
    # Measurement ceiling is actual model capability, not authorization for an
    # optimizer budget. The entire target and terminal EOS are recorded.
    encoded=encode_candidate(tokenizer,prompt,row['spec_text'],131072)
    rendered=tokenizer.apply_chat_template([dict(role='user',content=prompt)],tokenize=False,add_generation_prompt=True)
    prefix=tokenizer(rendered,add_special_tokens=False,truncation=False)['input_ids']
    if encoded['input_ids'][:len(prefix)]!=prefix or encoded['rendered_prompt']!=rendered:raise ValueError('Exact inference/training prefix mismatch')
    return dict(prompt=prompt,prompt_sha256=sha(prompt.encode()),description=description,
        response=row['spec_text'],response_sha256=sha(row['spec_text'].encode()),encoding=encoded,
        full_tokens=len(encoded['input_ids']),overage_9216=max(0,len(encoded['input_ids'])-9216),
        output_budget_16384_overage=max(0,encoded['response_tokens']-16384),truncation=False,
        task_shape='Existing FramingA NL/config-signature to entire module only; no cfg/property trailer target')


def summarize(rows,complete):
    if len(rows)!=COUNT or [r['index'] for r in rows]!=indices():raise ValueError('All128 original selected keys required')
    return dict(complete=complete,selected_candidates=COUNT,source_population=TOTAL,
        accounted_candidates=len(rows),selection_method='floor(i*(5010-1)/(128-1)), i=0..127; before all outcome/length checks',
        lexically_clear=sum((r.get('exclusions') or {}).get('status')=='lexically_clear' for r in rows),
        lexical_excluded=sum((r.get('exclusions') or {}).get('status')=='excluded_lexical_overlap' for r in rows),
        exclusion_unknown=sum((r.get('exclusions') or {}).get('status') not in ('lexically_clear','excluded_lexical_overlap') for r in rows),
        encoded_candidates=sum(r.get('encoded') is not None for r in rows),
        sany_checks_performed=0,sany_outcomes_unknown=COUNT,training_authorized=False,training_ready=False,
        training42_unchanged=True,proof_claim=False,nonvacuity_claim=False,generalization_claim=False)


def build(output):
    output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    before=inventory();source_before=source_identity()
    if digest(before)!=INPUTS_SHA:raise ValueError('Frozen complete corpus/input inventory drift')
    rows=[dict(r,exclusions=None,encoded=None,sany_status='unmeasured',target_sany_check_readiness='not_audited',
        historical_survived=r['raw'].get('survived'),historical_survived_recorded='survived' in r['raw']) for r in candidates()]
    dump(output/'rows.json',rows);dump(output/'summary.json',summarize(rows,False))
    dump(output/'identity_before.json',dict(inputs=before,sources=source_before))
    sources,goals,evidence=protected();dump(output/'protected_evidence.json',evidence)
    source_pool=pool(sources);goal_pool=pool(goals)
    from transformers import AutoTokenizer
    tokenizer=AutoTokenizer.from_pretrained(framing.TOKENIZER,local_files_only=True)
    for record in rows:
        record['exclusions']=exclusion_audit(record['raw'],source_pool,goal_pool)
        record['encoded']=encode(record['raw'],tokenizer)
        record['target_sany_check_readiness']='awaiting_review' if record['exclusions']['status']=='lexically_clear' else 'blocked_by_exclusion_audit'
        dump(output/'rows.json',rows);dump(output/'summary.json',summarize(rows,False))
    _,_,after_protected=protected();after=dict(inputs=inventory(),sources=source_identity())
    dump(output/'identity_after.json',after)
    if after!=dict(inputs=before,sources=source_before) or evidence!=after_protected:raise ValueError('Source/protected/input drift during audit')
    summary=summarize(rows,True);summary.update(rows_sha256=file_sha(output/'rows.json'),
        protected_evidence_sha256=file_sha(output/'protected_evidence.json'),
        max_full_tokens=max(r['encoded']['full_tokens'] for r in rows),
        over_9216=sum(r['encoded']['overage_9216']>0 for r in rows),identity_stable=True)
    dump(output/'summary.json',summary);return summary


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    try:print(json.dumps(build(a.output)))
    except BaseException as exc:
        if a.output.is_dir():dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc),training_ready=False))
        raise


if __name__=='__main__':main()
