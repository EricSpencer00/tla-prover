"""CPU gradient accumulation/AdamW candidate; caller owns rollout provenance.

This is a new implementation, not a bitwise GPU-optimizer equivalence claim.
No scoring, packet admission, file writes or optimizer-state resume occurs here.
"""
from copy import deepcopy
import math
from tools.proof_token_rl_objective import group_advantages

HYPERPARAMETERS=dict(lr=1e-6,betas=(.9,.999),eps=1e-8,weight_decay=0,foreach=False,
                     amsgrad=False,maximize=False,capturable=False,differentiable=False,fused=None)


class CPUGradientUpdate:
    def __init__(self,selected,rewards):
        import torch
        if len(rewards)!=32:raise ValueError('Full32 reward denominator required')
        ids=[r.get('sample_id') for r in rewards]
        if any(not isinstance(i,str) or not i for i in ids) or len(set(ids))!=32:
            raise ValueError('Exactly32 unique sample IDs required')
        if len(selected)!=9 or any(not isinstance(n,str) or not isinstance(p,torch.nn.Parameter) or
            p.dtype!=torch.float32 or not p.requires_grad or not bool(torch.isfinite(p).all())
            for n,p in selected.items()):raise ValueError('Nine finite enabled FP32 parameters required')
        if len({str(p.device) for p in selected.values()})!=1:raise ValueError('One parameter device required')
        if any(p.grad is not None for p in selected.values()):raise ValueError('Clear prior gradients before accumulation')
        self.selected=dict(selected);self.initial={n:p.detach().cpu().clone() for n,p in selected.items()}
        self.groups=[group_advantages(rewards[i:i+4]) for i in range(0,32,4)]
        count=sum(g['eligible'] for g in self.groups)
        self.requests=[dict(sample_id=ids[4*i+j],group_index=i,sample_index=j,
                            coefficient=-g['advantages'][j]/(4*count))
                       for i,g in enumerate(self.groups) if g['eligible'] for j in range(4)]
        self.accumulated={n:torch.zeros_like(p,device='cpu') for n,p in self.initial.items()}
        self.ledger=[];self.failed=False;self.prepared=None;self.committed=False

    def _unchanged(self):
        import torch
        if set(self.selected)!=set(self.initial) or any(p.dtype!=torch.float32 or
            not p.requires_grad or p.shape!=self.initial[n].shape or
            not torch.equal(p.detach().cpu(),self.initial[n]) for n,p in self.selected.items()):
            raise ValueError('Exact parent weights/parameter layout changed before commit')

    def accumulate(self,sample_id):
        """Consume an unweighted summed-logprob backward; always clear its grads."""
        import torch
        try:
            if self.failed or self.prepared is not None or self.committed:raise ValueError('Inactive accumulation state')
            self._unchanged()
            if len(self.ledger)>=len(self.requests) or self.requests[len(self.ledger)]['sample_id']!=sample_id:
                raise ValueError('Exact required response order/completeness required')
            request=self.requests[len(self.ledger)];metadata={}
            for name,p in self.selected.items():
                grad=p.grad
                if (grad is None or grad.dtype!=torch.float32 or grad.shape!=p.shape or
                    grad.device!=p.device or grad.is_sparse or not bool(torch.isfinite(grad).all())):
                    raise ValueError('All nine finite dense FP32 shape-matched response gradients required')
                metadata[name]=dict(dtype=str(grad.dtype),shape=list(grad.shape),elements=grad.numel(),
                                    source_device=str(grad.device),norm=float(grad.norm()))
                if not math.isfinite(metadata[name]['norm']):raise ValueError('Finite gradient norm required')
            # All inputs validated before mutating the aggregate; a failure still
            # permanently poisons this object, so no partial aggregate can step.
            for name,p in self.selected.items():
                self.accumulated[name].add_(p.grad.detach().to('cpu'),alpha=request['coefficient'])
                if not bool(torch.isfinite(self.accumulated[name]).all()):raise ValueError('Nonfinite CPU aggregate')
            row=dict(**request,gradients=metadata);self.ledger.append(row);return deepcopy(row)
        except Exception:
            self.failed=True;raise
        finally:
            for p in self.selected.values():p.grad=None

    def prepare(self):
        """Return CPU child/optimizer tensors; do not mutate model parameters."""
        import torch
        if self.failed or self.prepared is not None or self.committed:raise ValueError('Inactive update state')
        self._unchanged()
        if len(self.ledger)!=len(self.requests):raise ValueError('Missing required response gradients; no optimizer')
        if any(p.grad is not None for p in self.selected.values()):raise ValueError('Unconsumed device gradients')
        summary=dict(implementation='cpu_unweighted_response_gradient_accumulation_fresh_cpu_adamw_v1',
            actual_updates=0,eligible_groups=sum(g['eligible'] for g in self.groups),groups=deepcopy(self.groups),
            requested_samples=32,required_gradient_samples=len(self.requests),
            accounted_gradient_samples=len(self.ledger),ledger=deepcopy(self.ledger),
            optimizer_fresh=True,optimizer_device='cpu',clip_norm=1.,hyperparameters=dict(HYPERPARAMETERS))
        if not self.requests:
            self.prepared=dict(summary=summary,trainable_state=None,optimizer_state=None)
            return self.prepared
        params={n:torch.nn.Parameter(p.clone()) for n,p in self.initial.items()}
        for n,p in params.items():p.grad=self.accumulated[n].clone()
        norm=torch.nn.utils.clip_grad_norm_(list(params.values()),1.,error_if_nonfinite=True)
        if not math.isfinite(float(norm)) or float(norm)<=0:raise ValueError('Nonzero finite CPU policy gradient required')
        optimizer=torch.optim.AdamW(list(params.values()),**HYPERPARAMETERS)
        if optimizer.state:raise ValueError('Fresh empty optimizer required')
        optimizer.step()
        state={n:p.detach().clone() for n,p in params.items()}
        if any(not bool(torch.isfinite(p).all()) for p in state.values()):raise ValueError('Nonfinite CPU child')
        delta=math.sqrt(sum(float((state[n].double()-p.double()).square().sum()) for n,p in self.initial.items()))
        if not math.isfinite(delta) or delta<=0:raise ValueError('Actual nonzero finite child delta required')
        summary.update(actual_updates=1,gradient_norm=float(norm),parameter_delta_l2=delta)
        self.prepared=dict(summary=summary,trainable_state=state,optimizer_state=optimizer.state_dict())
        validate_prepared(self.prepared,self.initial)
        self._unchanged();return self.prepared

    def commit(self):
        """Apply prepared child only after full response and state validation."""
        import torch
        if self.failed or self.prepared is None or self.committed:raise ValueError('Prepared single commit required')
        self._unchanged()
        validate_prepared(self.prepared,self.initial)
        if self.prepared['summary']['groups']!=self.groups:raise ValueError('Prepared reward groups changed')
        if self.prepared['summary']['ledger']!=self.ledger:raise ValueError('Prepared response ledger changed')
        if [{key:row[key] for key in request} for row,request in zip(self.ledger,self.requests)]!=self.requests:
            raise ValueError('Prepared request order/coefficients changed')
        if self.prepared['summary']['actual_updates']==0:return self.prepared['summary']
        with torch.no_grad():
            for n,p in self.selected.items():p.copy_(self.prepared['trainable_state'][n])
        if any(not torch.equal(p.detach().cpu(),self.prepared['trainable_state'][n]) for n,p in self.selected.items()):
            raise ValueError('Exact device child application failed')
        self.committed=True;return self.prepared['summary']


def validate_prepared(prepared,parent):
    """Validate a CPU artifact, including after caller-controlled serialization."""
    import torch
    summary=prepared['summary'];groups=summary['groups'];eligible=sum(g['eligible'] for g in groups)
    if (len(groups)!=8 or summary['requested_samples']!=32 or summary['eligible_groups']!=eligible or
        summary['required_gradient_samples']!=4*eligible or summary['accounted_gradient_samples']!=4*eligible or
        len(summary['ledger'])!=4*eligible):raise ValueError('Full group/response accounting required')
    requests=[]
    for index,g in enumerate(groups):
        if g.get('group_size')!=4 or g.get('temperature')!=1. or type(g.get('eligible')) is not bool:
            raise ValueError('Frozen G4 reward group contract required')
        if not g['eligible']:continue
        rewards=g.get('rewards')
        if (not isinstance(rewards,list) or len(rewards)!=4 or any(type(r) not in (int,float) or r not in (0,1) for r in rewards)):
            raise ValueError('Binary complete group rewards required')
        advantages=[r-sum(rewards)/4 for r in rewards]
        if not any(advantages) or g.get('advantages')!=advantages or g.get('reward_variance')!=sum(a*a for a in advantages)/4:
            raise ValueError('Exact nonzero centered group advantages required')
        requests.extend(dict(group_index=index,sample_index=j,coefficient=-a/(4*eligible)) for j,a in enumerate(advantages))
    seen=set()
    for row,request in zip(summary['ledger'],requests):
        if any(row.get(k)!=v for k,v in request.items()) or not isinstance(row.get('sample_id'),str) or row['sample_id'] in seen:
            raise ValueError('Exact ordered response coefficients required')
        seen.add(row['sample_id'])
    if not eligible:
        if summary['actual_updates']!=0 or prepared['optimizer_state'] is not None or prepared['trainable_state'] is not None:
            raise ValueError('Excluded rewards must not construct optimizer')
        return summary
    child=prepared['trainable_state'];optimizer=prepared['optimizer_state']
    if (summary['actual_updates']!=1 or summary['optimizer_fresh'] is not True or summary['optimizer_device']!='cpu' or
        summary['clip_norm']!=1. or summary['hyperparameters']!=HYPERPARAMETERS or
        not math.isfinite(summary['gradient_norm']) or summary['gradient_norm']<=0 or len(parent)!=9 or set(child)!=set(parent)):
        raise ValueError('Exact one-step CPU optimizer contract required')
    for n,p in child.items():
        if p.device.type!='cpu' or p.dtype!=torch.float32 or p.shape!=parent[n].shape or not bool(torch.isfinite(p).all()):
            raise ValueError('Finite exact-layout CPU child required')
    delta=math.sqrt(sum(float((child[n].double()-p.double()).square().sum()) for n,p in parent.items()))
    if delta<=0 or not math.isfinite(delta) or delta!=summary['parameter_delta_l2']:raise ValueError('Actual child delta mismatch')
    if len(optimizer['param_groups'])!=1 or len(optimizer['state'])!=9:raise ValueError('All nine fresh AdamW states required')
    group=optimizer['param_groups'][0]
    if (any(group.get(k)!=v for k,v in HYPERPARAMETERS.items()) or len(group['params'])!=9 or
        any(type(i) is not int for i in group['params']) or len(set(group['params']))!=9 or
        set(group['params'])!=set(optimizer['state'])):
        raise ValueError('CPU AdamW hyperparameter mismatch')
    for ident,p in zip(group['params'],parent.values()):
        state=optimizer['state'][ident]
        step=state['step']
        if (not isinstance(step,torch.Tensor) or step.ndim!=0 or step.dtype!=torch.float32 or
            step.device.type!='cpu' or not bool(torch.isfinite(step)) or float(step)!=1):
            raise ValueError('Exactly one scalar FP32 CPU optimizer step required')
        for key in ('exp_avg','exp_avg_sq'):
            value=state[key]
            if value.device.type!='cpu' or value.dtype!=torch.float32 or value.shape!=p.shape or not bool(torch.isfinite(value).all()):
                raise ValueError('Finite CPU optimizer moments required')
    return summary
