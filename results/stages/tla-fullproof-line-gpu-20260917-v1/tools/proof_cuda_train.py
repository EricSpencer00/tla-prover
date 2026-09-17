#!/usr/bin/env python3
"""TRAIN-only response SFT: frozen CUDA bf16 Llama8B, float32 final layer.

No RL, no verifier reward, no benchmark answers. Preparation is local/read-only
with respect to its sources; training requires a hash-pinned prepared packet.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import random
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.proof_sequence_train import training_tasks, restore_trainable
from tools.proof_candidate_rank import encode_candidate
from tools.proof_repair_pilot import prompt_for, with_dependency_context

ALGORITHM = 'response-only causal cross-entropy SFT; fresh float32 AdamW; no RL'
PROFILE = 'frozen bf16 base with float32 final transformer layer; bf16 autocast'
HIERARCHICAL_MANIFEST = 'c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda:stream.read(8*1024*1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')


def model_files(model_path):
    paths = sorted(p for p in Path(model_path).iterdir() if p.is_file() and
                   (p.suffix in ('.json', '.safetensors') or p.name in ('tokenizer.model','chat_template.jinja')))
    if not any(p.suffix=='.safetensors' for p in paths):
        raise ValueError('Expected cached safetensors base model')
    return {p.name:file_sha(p) for p in paths}


def select_final_layer(net, train=False):
    """Identical mixed-dtype profile for BASE and trained inference."""
    import torch
    net.eval().requires_grad_(False)
    layer = net.model.layers[-1]
    layer.to(dtype=torch.float32)
    layer.requires_grad_(train)
    ids = {id(p) for p in layer.parameters()}
    selected = {name:p for name,p in net.named_parameters() if id(p) in ids}
    if not selected or any(p.dtype!=torch.float32 for p in selected.values()):
        raise ValueError('Final transformer layer must be nonempty float32')
    return selected


def load_policy(model_path, device='cuda'):
    import torch
    import transformers
    if device != 'cuda' or not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError('This Llama8B runtime requires CUDA bf16 support')
    config = transformers.AutoConfig.from_pretrained(model_path, local_files_only=True)
    if (config.model_type,config.num_hidden_layers,config.hidden_size) != ('llama',32,4096):
        raise ValueError('Expected cached Llama3.1-8B architecture; no model fallback')
    net = transformers.AutoModelForCausalLM.from_pretrained(
        model_path, local_files_only=True, torch_dtype=torch.bfloat16,
        attn_implementation='sdpa').to(device).eval()
    select_final_layer(net, train=False)
    return net


def restore_policy(net, saved, expected_model_files):
    if saved['config']['model_files'] != expected_model_files or saved['config']['dtype_profile'] != PROFILE:
        raise ValueError('Checkpoint base model/dtype profile mismatch')
    selected = select_final_layer(net, train=False)
    restore_trainable(selected, saved)
    return selected


def schedule(count, steps, seed):
    if not 1 <= count <= 256 or not 1 <= steps <= 100:
        raise ValueError('Bounded nonempty population and at most100 updates required')
    rng = random.Random(seed); result=[]
    while len(result)<steps:
        epoch=list(range(count)); rng.shuffle(epoch); result.extend(epoch)
    return result[:steps]


def encode_row(tokenizer, row, max_tokens=8192):
    if not 1 <= max_tokens <= 8192:
        raise ValueError('Maximum context8192; no truncation')
    encoded = encode_candidate(tokenizer, row['prompt'], row['response'], max_tokens)
    if encoded['response_tokens'] < 3:
        raise ValueError('Multi-token proof response plus EOS required')
    return encoded


def validate_packet(packet):
    if packet.get('packet_kind') == 'frozen32_broader_whole_target_proofs':
        from tools.proof_broader_packet import validate_training_packet
        return validate_training_packet(packet)
    if packet.get('packet_kind') == 'frozen6_whole_target_proofs':
        # A separate evidence-bound contract, not a relaxation of historical
        # fifty-leaf or seventeen-repair population checks.
        from tools.proof_whole_packet import validate_training_packet
        return validate_training_packet(packet)
    if packet.get('algorithm')!=ALGORITHM or packet.get('split')!='train' or packet.get('evaluation_responses_exported') is not False:
        raise ValueError('Only explicit TRAIN SFT packets allowed')
    hierarchical = packet.get('packet_kind') == 'frozen17_hierarchical_repair_spans'
    if packet.get('packet_kind') not in (None, 'frozen17_hierarchical_repair_spans'):
        raise ValueError('Unknown TRAIN packet contract')
    count = 17 if hierarchical else 50
    rows=packet['rows']
    if len(rows)!=count or len({r['id'] for r in rows})!=count:
        raise ValueError('Exact verified TRAIN population required: '+str(count))
    fields={'id','split','source_family','source_sha256','assembled_sha256','prompt','prompt_sha256','response','response_sha256'}
    for row in rows:
        if set(row)!=fields or row['split']!='train' or not row['source_family']:
            raise ValueError('Unexpected row fields or non-training split')
        for text in ('prompt','response'):
            if not row[text] or sha(row[text].encode())!=row[text+'_sha256']:
                raise ValueError('Prompt/response hash mismatch')
        if any(not re_full_sha(row[k]) for k in ('source_sha256','assembled_sha256')):
            raise ValueError('Source/assembled hashes required')
    if packet['train_ids'] != [r['id'] for r in rows]:
        raise ValueError('Training ID order mismatch')
    evidence=packet['evidence']
    populations = {'original18','official119','official30'} | ({'development'} if hierarchical else set())
    if set(evidence['populations'])!=populations or evidence['threshold']!=.65:
        raise ValueError('All original18/119/30 exclusion evidence required')
    for population,count in [('original18',18),('official119',119),('official30',30)]:
        members=evidence['populations'][population]
        identifiers=[r if isinstance(r,str) else r['id'] for r in members]
        if len(identifiers)!=count or len(set(identifiers))!=count:
            raise ValueError('Full unique exclusion populations required')
    if evidence['manifest_sha256']!=packet['manifest_sha256'] or evidence['strict_controls_verified'] is not True:
        raise ValueError('Evidence must bind exact controlled training manifest')
    required_hashes = ('manifest_sha256','controls_sha256') + (
        ('original18_eval_sha256','original18_reference_blob_sha256','verifier_identity_sha256')
        if hierarchical else ('original18_audit_sha256',))
    for key in required_hashes:
        if not re_full_sha(evidence[key]):
            raise ValueError('Missing evidence hash')
    if not math.isfinite(evidence['max_jaccard']) or not 0<=evidence['max_jaccard']<.65 or evidence['canonical_matches']!=0:
        raise ValueError('Evaluation contamination detected')
    if hierarchical:
        validate_hierarchical_evidence(packet)
    return rows


def validate_hierarchical_evidence(packet):
    """Explicit new17-span contract; historical50-row packets stay unchanged.

    Preparation performs local source/control attestation; remote training
    consumes only the caller's hash-pinned packet, never held-out responses.
    """
    evidence=packet['evidence']; rows=packet['rows']
    expected_shape=dict(train_spans=17,leaf_spans=6,hierarchical_spans=11,source_families=3,
                        independent_theorem_count_claimed=False,whole_target_generation=False)
    if (packet.get('schema_version')!=1 or packet.get('training_ready') is not True or
            packet['manifest_sha256']!=HIERARCHICAL_MANIFEST or packet.get('task_shape')!=expected_shape or
            len({r['source_family'] for r in rows})!=3 or
            sum('\n' in r['response'] for r in rows)!=11):
        raise ValueError('Fresh exact17 hierarchical TRAIN contract required')
    dev=evidence['populations']['development']
    if len(dev)!=4 or len(set(dev))!=4 or set(dev)&set(packet['train_ids']):
        raise ValueError('Full distinct four-task development exclusion required')
    identity=evidence.get('verifier_identity')
    if (not isinstance(identity,dict) or identity.get('complete') is not True or
            identity.get('manifest_sha256')!=packet['manifest_sha256'] or
            identity.get('controls_sha256')!=evidence['controls_sha256'] or
            identity.get('requested_controls')!=34 or identity.get('completed_controls')!=34 or
            not identity.get('before') or identity['before']!=identity.get('after') or
            sha((json.dumps(identity,indent=2)+'\n').encode())!=evidence['verifier_identity_sha256']):
        raise ValueError('Fresh complete unchanged verifier identity required')
    controls=evidence.get('controls',[])
    if len(controls)!=17 or {c['id'] for c in controls}!=set(packet['train_ids']):
        raise ValueError('Exact17 positive control bindings required')
    by_id={r['id']:r for r in rows}
    for control in controls:
        if (control['proved']!=control['total'] or control['total']<=0 or
                control['assembled_sha256']!=by_id[control['id']]['assembled_sha256'] or
                control['candidate_sha256']!=control['assembled_sha256'] or
                not {'--strict','--nofp'}.issubset(control.get('command',[]))):
            raise ValueError('Strict positive control must bind exact training module')
    if evidence.get('original18_reference_text_exported') is not False:
        raise ValueError('Archived evaluation answers cannot be exported')


def re_full_sha(value):
    return isinstance(value,str) and len(value)==64 and all(c in '0123456789abcdef' for c in value)


def prepare(manifest_path, controls_path, original18_audit, output):
    raw=manifest_path.read_bytes(); manifest=json.loads(raw)
    train=training_tasks(manifest)
    if len(train)!=50 or manifest.get('kind')!='exact_human_proof_leaf_expansion':
        raise ValueError('This bounded preflight requires the verified50 leaf manifest')
    controls_raw=controls_path.read_bytes(); controls=json.loads(controls_raw)
    if {r['id'] for r in controls}!={t['id'] for t in train} or len(controls)!=50:
        raise ValueError('Exact50 control rows required')
    by_id={r['id']:r for r in controls}
    maxima=[]; rows=[]
    for t in train:
        assembled=t['prefix']+t['reference_fragment']+t['suffix']
        if sha(assembled.encode())!=t['assembled_sha256'] or file_sha(t['source_path'])!=t['source_sha256']:
            raise ValueError('Training source/assembled bytes changed')
        c=by_id[t['id']]; good=c['reference']; bad=c['omitted']
        if not (c['admitted'] and c['assembled_sha256']==t['assembled_sha256'] and
                good['certified'] and good['returncode']==0 and good['proved']==good['total']>0 and
                not good.get('timed_out') and good['sha256']==t['assembled_sha256'] and
                not bad['certified'] and bad['status']=='contract_reject'):
            raise ValueError('Strict positive/negative reference controls required')
        if not {'--strict','--nofp'}.issubset(good.get('command',[])):
            raise ValueError('Strict uncached verifier command required')
        if file_sha(good['candidate_path'])!=t['assembled_sha256']:
            raise ValueError('Controlled candidate artifact changed')
        for key in ('decontamination','development_similarity'):
            if not t.get(key):
                raise ValueError('Missing manifest exclusion evidence')
            maxima.extend(v['max_jaccard'] for v in t[key].values())
        for dep in t.get('dependencies',[]):
            if file_sha(dep)!=t['dependency_sha256'][dep]:
                raise ValueError('Dependency changed')
        prompt=prompt_for(with_dependency_context(t)); response=t['reference_fragment']
        rows.append(dict(id=t['id'],split='train',source_family=t['source_family'],
            source_sha256=t['source_sha256'],assembled_sha256=t['assembled_sha256'],
            prompt=prompt,prompt_sha256=sha(prompt.encode()),response=response,response_sha256=sha(response.encode())))
    populations={kind:[] for kind in ('official119','official30')}
    for entry in manifest['official_sources']:
        kind=entry['id'].split(':')[0]
        if kind not in populations or file_sha(entry['path'])!=entry['sha256']:
            raise ValueError('Official source exclusions changed')
        populations[kind].append(dict(id=entry['id'],sha256=entry['sha256']))
    if any(len(populations[k])!=n or len({r['id'] for r in populations[k]})!=n for k,n in [('official119',119),('official30',30)]):
        raise ValueError('Full119/30 exclusion populations required')
    audit_raw=original18_audit.read_bytes(); audit=json.loads(audit_raw)
    if audit['manifest_hashes'].get(str(manifest_path.resolve()))!=sha(raw):
        raise ValueError('Original18 audit does not bind training manifest')
    comparison=audit['comparisons']['train50']
    if len(comparison)!=18 or len({r['id'] for r in comparison})!=18 or audit['threshold']!=.65:
        raise ValueError('Exact original18 audit required')
    exact=sum(len(r['canonical_exact_matches']) for r in comparison)
    maxima.extend(r[k]['max_jaccard'] for r in comparison for k in ('prompt','original_reference_module','named_goal'))
    evidence=dict(populations={**populations,'original18':[r['id'] for r in comparison]},
        threshold=.65,max_jaccard=max(maxima),canonical_matches=exact,
        manifest_sha256=sha(raw),controls_sha256=sha(controls_raw),original18_audit_sha256=sha(audit_raw),
        links=dict(manifest=str(manifest_path.resolve()),controls=str(controls_path.resolve()),original18_audit=str(original18_audit.resolve())),
        strict_controls_verified=True,pretraining_caveat='Excludes these local training sources; unknown base pretraining not certified')
    packet=dict(algorithm=ALGORITHM,split='train',manifest_sha256=sha(raw),evidence=evidence,
                evaluation_responses_exported=False,train_ids=[r['id'] for r in rows],rows=rows)
    validate_packet(packet)
    output.mkdir(parents=True,exist_ok=False); dump(output/'train.json',packet)
    dump(output/'summary.json',dict(train_tasks=50,train_packet_sha256=file_sha(output/'train.json'),
         evaluation_responses_exported=False,algorithm=ALGORITHM,training_executed=False))
    return packet


def autocast(device):
    import torch
    return torch.autocast(device_type=device,dtype=torch.bfloat16)


def release_unused_cache(device, enabled):
    """Bound allocator fragmentation between variable-length whole-proof steps.

    This cannot free live model/optimizer tensors and never weakens the peak
    memory guard. Only the explicit whole-proof contract enables it.
    """
    if enabled:
        if device != 'cuda':
            raise ValueError('CUDA cache policy requires CUDA')
        import torch
        torch.cuda.empty_cache()


def train_steps(net, selected, encoded, rows, steps, seed, lr, seconds, device, emit, clear_cache=False):
    import torch
    if not math.isfinite(lr) or lr<=0 or not 0<seconds<=600:
        raise ValueError('Positive finite learning rate and at most600 seconds required')
    indices=schedule(len(encoded),steps,seed)
    if any(p.dtype!=torch.float32 or not p.requires_grad for p in selected.values()):
        raise ValueError('Only enabled float32 final-layer parameters may train')
    optimizer=torch.optim.AdamW(selected.values(),lr=lr,weight_decay=0,foreach=False)
    started=time.monotonic(); metrics=[]
    net.eval()
    for step,index in enumerate(indices):
        if time.monotonic()-started>=seconds:
            break
        e=encoded[index]; ids=torch.tensor([e['input_ids']],device=device)
        labels=torch.tensor([e['labels']],device=device)
        optimizer.zero_grad(set_to_none=True)
        with autocast(device):
            loss=net(input_ids=ids,labels=labels,use_cache=False).loss
        if not torch.isfinite(loss):
            raise RuntimeError('Nonfinite loss')
        loss.backward()
        norm=torch.nn.utils.clip_grad_norm_(selected.values(),1.,error_if_nonfinite=True)
        optimizer.step()
        if any(not torch.isfinite(p).all() for p in selected.values()):
            raise RuntimeError('Nonfinite parameter')
        release_unused_cache(device,clear_cache)
        row=dict(step=step+1,task=rows[index]['id'],loss=float(loss.detach()),
                 gradient_norm=float(norm),response_tokens=e['response_tokens'],elapsed_s=time.monotonic()-started)
        metrics.append(row); emit(row)
    return optimizer,metrics,indices


def save_reload(net, selected, optimizer, initial, config, metrics, probe_ids, checkpoint, device):
    import torch
    state={n:p.detach().cpu().clone() for n,p in selected.items()}
    saved=dict(trainable_state=state,optimizer=optimizer.state_dict(),config=config,metrics=metrics,
               torch_rng_state=torch.get_rng_state(),python_rng_state=random.getstate(),
               cuda_rng_state=torch.cuda.get_rng_state_all() if device=='cuda' else None)
    torch.save(saved,checkpoint)
    probe=torch.tensor([probe_ids],device=device)
    with torch.no_grad(),autocast(device):
        before=net(input_ids=probe,use_cache=False).logits[:,-1].cpu().clone()
        for parameter in selected.values():parameter.zero_()
        restored=torch.load(checkpoint,map_location='cpu',weights_only=False)
        restore_trainable(selected,restored)
        exact_tensors=all(torch.equal(p.detach().cpu(),state[n]) for n,p in selected.items())
        after=net(input_ids=probe,use_cache=False).logits[:,-1].cpu()
    if not exact_tensors or not torch.equal(before,after):
        raise RuntimeError('Checkpoint failed exact same-runtime reload')
    delta=sum(float((state[n]-initial[n]).double().square().sum()) for n in state)**.5
    return dict(reload_tensors_exact=exact_tensors,reload_logits_exact=True,parameter_delta_l2=delta,
                checkpoint_sha256=file_sha(checkpoint))


def train(args):
    os.environ.update(HF_HUB_OFFLINE='1',TRANSFORMERS_OFFLINE='1',TOKENIZERS_PARALLELISM='false')
    raw=args.input.read_bytes()
    if sha(raw)!=args.expected_input_sha256:
        raise ValueError('Prepared packet SHA mismatch')
    packet=json.loads(raw); rows=validate_packet(packet)
    schedule(len(rows),args.steps,args.seed)
    if not 1<=args.seconds<=600 or not 1<=args.max_tokens<=8192 or not math.isfinite(args.lr) or args.lr<=0:
        raise ValueError('Invalid bounded training budgets')
    import torch
    import transformers
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError('CUDA bf16 is required; no CPU/model fallback')
    started=time.monotonic(); random.seed(args.seed); torch.manual_seed(args.seed); torch.cuda.manual_seed_all(args.seed)
    torch.backends.cuda.matmul.allow_tf32=False
    tokenizer=transformers.AutoTokenizer.from_pretrained(args.model_path,local_files_only=True)
    encoded=[encode_row(tokenizer,row,args.max_tokens) for row in rows]
    hashes=model_files(args.model_path)
    args.output.mkdir(parents=True,exist_ok=False); (args.output/'train.json').write_bytes(raw)
    config=dict(algorithm=ALGORITHM,dtype_profile=PROFILE,input_sha256=sha(raw),model_path=str(args.model_path),
        model_files=hashes,seed=args.seed,lr=args.lr,requested_updates=args.steps,seconds=args.seconds,max_tokens=args.max_tokens,
        train_ids=[r['id'] for r in rows],task_schedule=[rows[i]['id'] for i in schedule(len(rows),args.steps,args.seed)],
        hypothesis='Llama8B final-layer supervised proof-fragment learning improves separately measured transfer',
        stop='At most100 shuffled updates;600s total worker deadline including startup,90s soft reserve for checkpoint; supervisor terminates on timeout',
        measurement='SFT updates/coverage/loss/gradients/reload; no proof-success claim without external strict evaluation',
        torch_version=torch.__version__,transformers_version=transformers.__version__,hardware=torch.cuda.get_device_name(),
        evidence=packet['evidence'],implementation_sha256={str(p.relative_to(ROOT)):file_sha(p) for p in
            [Path(__file__),ROOT/'tools/proof_sequence_train.py',ROOT/'tools/proof_candidate_rank.py',ROOT/'tools/proof_repair_pilot.py']})
    if packet.get('packet_kind') == 'frozen6_whole_target_proofs':
        config['implementation_sha256']['tools/proof_whole_packet.py'] = file_sha(ROOT/'tools/proof_whole_packet.py')
        config['cuda_cache_policy'] = 'release_unused_after_each_optimizer_step'
    if packet.get('packet_kind') == 'frozen32_broader_whole_target_proofs':
        for name in ('proof_broader_packet.py', 'proof_whole_packet.py'):
            config['implementation_sha256']['tools/'+name] = file_sha(ROOT/'tools'/name)
        config['cuda_cache_policy'] = 'release_unused_after_each_optimizer_step'
    dump(args.output/'config.json',config)
    dump(args.output/'encodings.json',[dict(id=r['id'],**e) for r,e in zip(rows,encoded)])
    torch.cuda.reset_peak_memory_stats(); net=load_policy(args.model_path)
    selected=select_final_layer(net,train=True)
    initial={n:p.detach().cpu().clone() for n,p in selected.items()}
    config.update(trainable_names=list(selected),trainable_dtypes={n:str(p.dtype) for n,p in selected.items()},
                  trainable_parameters=sum(p.numel() for p in selected.values()),
                  all_parameter_dtypes=sorted({str(p.dtype) for p in net.parameters()}))
    dump(args.output/'config.json',config)
    remaining=max(.000001,args.seconds-(time.monotonic()-started)-90)
    with (args.output/'steps.jsonl').open('x') as ledger:
        def emit(row):
            ledger.write(json.dumps(row)+'\n');ledger.flush();print(json.dumps(row),flush=True)
        optimizer,metrics,_=train_steps(net,selected,encoded,rows,args.steps,args.seed,args.lr,remaining,'cuda',emit,
                                       clear_cache=packet.get('packet_kind') in (
                                           'frozen6_whole_target_proofs', 'frozen32_broader_whole_target_proofs'))
    checkpoint=args.output/'policy_optimizer.pt'
    result=save_reload(net,selected,optimizer,initial,config,metrics,encoded[0]['input_ids'],checkpoint,'cuda')
    summary=dict(**result,algorithm=ALGORITHM,updates=len(metrics),requested_updates=args.steps,
        train_tasks=len(rows),attempted_train_tasks=len({r['task'] for r in metrics}),
        family_coverage=sorted({r['source_family'] for r in rows if r['id'] in {m['task'] for m in metrics}}),
        elapsed_s=time.monotonic()-started,cuda_peak_allocated=torch.cuda.max_memory_allocated(),
        cuda_peak_reserved=torch.cuda.max_memory_reserved(),evaluation_responses_forwarded=0,
        checkpoint=str(checkpoint),stop_reason='step_budget' if len(metrics)==args.steps else 'time_budget')
    dump(args.output/'summary.json',summary);return summary


def supervise(args, argv):
    """Own the CUDA worker through exit/timeout without initializing CUDA here."""
    if not 1<=args.seconds<=600 or not 1<=args.steps<=100:
        raise ValueError('Maximum100 updates and600 seconds required')
    if args.output.exists():
        raise ValueError('Output must be new; never reuse an active or completed run')
    command=[sys.executable,str(Path(__file__).resolve()),'_worker',*argv]
    process=subprocess.Popen(command,start_new_session=True)
    def stop_worker():
        try:os.killpg(process.pid,signal.SIGTERM)
        except ProcessLookupError:pass
        try:process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid,signal.SIGKILL);process.wait(timeout=5)
    previous=signal.getsignal(signal.SIGTERM)
    def terminated(signum,frame):
        raise SystemExit(128+signum)
    signal.signal(signal.SIGTERM,terminated)
    try:
        return process.wait(timeout=args.seconds)
    except subprocess.TimeoutExpired:
        stop_worker()
        if args.output.exists():
            dump(args.output/'timeout.json',dict(status='supervisor_timeout',seconds=args.seconds,
                 certified=False,checkpoint_reload_unverified=True,
                 warning='Partial checkpoint files are not valid completion evidence'))
        return 124
    except BaseException:
        stop_worker()
        raise
    finally:
        signal.signal(signal.SIGTERM,previous)


def main():
    parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='mode',required=True)
    p=sub.add_parser('prepare');p.add_argument('--manifest',type=Path,required=True)
    p.add_argument('--controls',type=Path,required=True);p.add_argument('--original18-audit',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p=sub.add_parser('train',aliases=['_worker']);p.add_argument('--input',type=Path,required=True)
    p.add_argument('--expected-input-sha256',required=True);p.add_argument('--model-path',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--seed',type=int,required=True)
    p.add_argument('--steps',type=int,default=100);p.add_argument('--seconds',type=int,default=600)
    p.add_argument('--max-tokens',type=int,default=8192);p.add_argument('--lr',type=float,default=1e-5)
    args=parser.parse_args()
    if args.mode=='train':
        return supervise(args,sys.argv[2:])
    result=prepare(args.manifest,args.controls,args.original18_audit,args.output) if args.mode=='prepare' else train(args)
    print(json.dumps({'prepared':len(result['rows'])} if args.mode=='prepare' else result))


if __name__=='__main__':raise SystemExit(main() or 0)
