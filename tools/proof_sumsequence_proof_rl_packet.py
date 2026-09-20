"""One explicit proof-reward update contract; previous probes alone do not train."""
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
# Configures native expandable allocation before importing numerical libraries.
from tools import proof_sumsequence_compact_offload_probe as probe
from tools.proof_token_rl_objective import group_advantages

PATHS=probe.PATHS+('feedback','probe_results')
FEEDBACK_SHA='185107e8712dab5eb6d25d2126458fd7a247e1dd9f0504abc4c94d8b0fe3be89'
PROBE_FILES={
    'admission.json':'de0ece6d08d68aee82a1be8ac602d7e80d062643dc520951ca40eb6fab64fcdd',
    'allocator_after_load.json':'92c7b463a61743ac9c44016002d38973910b8721ffc8cbe218e8e57a0019de2e',
    'allocator_final.json':'2e563a56c2e7fc7d847151651d8bf5047ea55f79ad66d0b3c6c5e505353e7739',
    'events.jsonl':'80b1767e108e3b75428ec9284377171f336c6e35e6416de242f4787229d32530',
    'hardware.json':'7f189ad8dc690ec684f3ab3dac087d1a9cd41f43b2b6f02dc2edde3ca74169d1',
    'process.json':'7778a3eb89b79e3c3020061a4a758aee4cac167c9d89d8b701accfe5b1f558d1',
    'rows.json':'af62e2bfac6ada97a244b38de1f31f46d1a058cd3498438e319416badd2434b9',
    'summary.json':'e0277c2962a9df1eb4a0ecb63efab22e27dabfd6869c495b7bbb69eefc267dbb',
    'worker_summary.json':'7c274a7db3ee0ac5704cecedaf0711d87b5f40f4918610c7ba975c277e9a7795',
}
BUDGET=dict(seconds=900,seed=20261004,memory_limit=36*1024**3,host_memory_limit=64*1024**3,
    checkpoint_reserve=120,requested_samples=32,eligible_groups=1,gradient_samples=4,
    optimizer_updates=1,checkpoint_writes=1,new_generation=False,max_context=8192,
    max_logprob_error=.03,mean_logprob_error=.003,cpu_threads=4,
    optimizer=dict(lr=1e-6,betas=[.9,.999],eps=1e-8,weight_decay=0,foreach=False,
        amsgrad=False,maximize=False,capturable=False,differentiable=False,fused=None),
    clip_norm=1.,allocator=probe.ALLOCATOR_CONF,
    method='Saved same-policy grouped REINFORCE: unweighted full-EOS summed-logprob CUDA gradients; CPU weighting/accumulation, fresh CPU AdamW, compact scalars and exact saved-logprob offload. Not PPO/GRPO, not fresh online sampling, not bitwise GPU-optimizer equivalence.')
SOURCES=tuple(sorted(set(probe.SOURCES)|{
    'tools/proof_cpu_gradient_update.py','tools/proof_sumsequence_proof_rl_packet.py',
    'tools/proof_sumsequence_proof_rl_train.py','tools/proof_sumsequence_proof_rl_train.pbs',
    'tools/proof_sumsequence_feedback_packet.py'}))


def load(path):
    return json.loads(Path(path).read_bytes())


def validate_prerequisites(a,current):
    """Re-audit pinned successful GPU evidence and full strict proof feedback."""
    for name,pin in PROBE_FILES.items():
        if probe.train.file_sha(a.probe_results/name)!=pin:
            raise ValueError('Exact complete successful compact probe required: '+name)
    if current!=load(a.probe_results/'admission.json'):
        raise ValueError('Actual current inputs differ from successful GPU admission')
    rollouts=[json.loads(line) for line in a.rollouts.read_bytes().splitlines()]
    selected=probe.select_rows(rollouts)
    probe.validate_results(selected,load(a.probe_results/'rows.json'))
    summary=load(a.probe_results/'summary.json')
    process=load(a.probe_results/'process.json')
    if (summary['complete'] is not True or summary['completed_samples']!=4 or
        summary['parent_unchanged'] is not True or summary['identity_stable'] is not True or
        summary['optimizer_updates']!=0 or summary['checkpoint_writes']!=0 or
        summary['new_generation'] is not False or not 0<summary['total_seconds']<=900 or
        process['returncode']!=0 or process['timed_out'] or not process['cleanup_complete'] or
        not process['root_reaped'] or process['surviving_owned_processes']):
        raise ValueError('Complete no-update GPU feasibility and owned termination required')
    if probe.guard_allocator(load(a.probe_results/'allocator_final.json'))!=summary['memory']:
        raise ValueError('Actual successful allocator evidence required')
    if probe.train.file_sha(a.feedback)!=FEEDBACK_SHA:
        raise ValueError('Exact independently re-audited full32 proof feedback required')
    feedback=load(a.feedback)
    evaluation=current['inference_admission']['evaluation']
    records=load(a.verified_rows)
    if (feedback['kind']!='verified_same_policy_proof_feedback' or
        feedback['policy_sha256']!=evaluation['policy_sha256'] or
        feedback['requested_samples']!=32 or feedback['accounted_samples']!=32 or
        feedback['training_authorized'] is not False or feedback['optimizer_updates']!=0 or
        feedback['packet_source_sha256']!=probe.train.file_sha(ROOT/'tools/proof_sumsequence_feedback_packet.py') or
        feedback['child_rollouts_sha256']!=probe.PINS['rollouts'] or
        len(records)!=64 or len(feedback['rewards'])!=32):
        raise ValueError('Unchanged complete same-policy proof-feedback prerequisite required')
    for request,raw,record,reward in zip(evaluation['requests'],rollouts,records[32:],feedback['rewards']):
        if (any(reward.get(k)!=v for k,v in request.items()) or record['arm']!='child' or
            record['sample_id']!=request['sample_id'] or reward['reward']!=record['proof'] or
            reward['proof_record_sha256']!=probe.digest(record) or
            reward['rollout_sha256']!=probe.digest(raw) or
            reward['finish_reason']!=raw['finish_reason']):
            raise ValueError('Every proof reward must bind its actual original response and strict record')
    groups=[group_advantages(feedback['rewards'][i:i+4]) for i in range(0,32,4)]
    if (groups!=feedback['groups'] or [i for i,g in enumerate(groups) if g['eligible']]!=[1] or
        groups[1]['rewards']!=[0,1,0,0] or groups[1]['advantages']!=[-.25,.75,-.25,-.25] or
        [r['sample_id'] for r in feedback['rewards'][4:8]]!=[r['sample_id'] for r in selected]):
        raise ValueError('Only original complete Barriers G4 proof variance admitted')
    return feedback


def admit(a):
    current=probe.admit(a)
    feedback=validate_prerequisites(a,current)
    return dict(schema=1,kind='one_same_policy_proof_reward_cpu_update',budget=BUDGET,
        probe_admission=current,feedback_sha256=FEEDBACK_SHA,feedback=feedback,
        successful_probe_files=PROBE_FILES,
        implementation_sha256={name:probe.train.file_sha(ROOT/name) for name in SOURCES},
        training_authorized=True,proof_success_claim=False,generalization_claim=False,
        provenance='Explicit new bounded training contract under the standing prover goal; original no-training inference/probe/feedback admissions remain prerequisites, not independently training authorization. Full strict64 feedback and controls were re-audited locally; the exact artifact is pinned here.',
        evaluation_required='Checkpoint restoration and matched parent/child SANY+strict-TLAPS retention; training or parameter change alone is not a capability gain.')
