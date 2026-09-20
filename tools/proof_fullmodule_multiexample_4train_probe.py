"""Four-training-row diversity variant of the bounded full-module probe.

This thin, append-only variant reuses the audited multi-example implementation
while changing only the pinned row partition.  Rows 42, 43, 44, and 49 are
optimized in fixed order; rows 47 and 107 remain eval-only.  No gate or
generalization claim is made.
"""
import argparse, hashlib, json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import proof_fullmodule_multiexample_probe as base

TRAIN_ROWS = (42, 43, 44, 49)
EVAL_ROWS = (47, 107)
ROW_IDS = {
    42: 'w4-fullmodule:w4opus::d14-m4-p0-t4',
    43: 'w4-fullmodule:w4opus::d13-m7-p1-t4',
    44: 'w4-fullmodule:w4opus::d0-m0-p1-t0',
    49: 'w4-fullmodule:w4opus::d1-m0-p0-t5',
    47: 'w4-fullmodule:w4opus::d2-m7-p4-t2',
    107: 'w4-fullmodule:w4opus::d3-m0-p0-t0',
}
RESPONSE_SHAS = {
    42: '39d35a34deda13d950e72efaf0641e1d6c0ef980a9d75bd8260a57290be1c910',
    43: '0adf63f07aa9367cc90de5f7d12d0be303549f42c660729dfa6e10620f1c8194',
    44: '1014e9b256c188e24ba4374d5125099d0af0475df5883896bdb41ca683bc7f94',
    49: '2167983adbb1e282fd81f4aeb4f6572acba44fa1db9abdb2e783c449cbd0c23c',
    47: '36c548d2a475c0d086ddf0340f927b36002699ce86e955d702e061324ad2f07c',
    107: '5f6b169dc010369d4e6f65b7766b7961e44a4df15790988c5763861a06e3e853',
}
PROMPT_SHAS = {
    42: '0ecccbd8c36e8a677ce18481315515a37c833e0cfc49a8967decb365e8d260aa',
    43: 'f9e2657fb1cb063995157768b18ce8393bf746d2e0ed0a8562c86a30914d60b1',
    44: 'edf78ead117f730819e6ee1b6b7058b01c648f3e6983f688f7ec5bbd0c7eceea',
    49: '92f72075fe6a6d07e1aafffaa3e8d4d560a056e8d5517bc33b5dd82aa98df732',
    47: '32eb750d7db375df72e8e93d929ac3e5c7a365d50a915202c62db6e3d675877f',
    107: '388d75fc27a48d38ccb3fd0258a72ddfd1b9dbb0852b0b058057521e8eaafb51',
}
BUDGET = dict(base.BUDGET, eval_rows=list(EVAL_ROWS), train_only=False,
              gate_claim=False, generalization_claim=False, proof_claim=False,
              tlc_claim=False, nonvacuity_claim=False)


def _configure():
    """Point audited implementation globals at this immutable variant."""
    base.TRAIN_ROWS = TRAIN_ROWS
    base.EVAL_ROWS = EVAL_ROWS
    base.ROW_IDS = ROW_IDS
    base.RESPONSE_SHAS = RESPONSE_SHAS
    base.PROMPT_SHAS = PROMPT_SHAS
    base.BUDGET = BUDGET
    base.SOURCES = tuple(sorted(set(base.SOURCES) | {'tools/proof_fullmodule_multiexample_4train_probe.py'}))
    base.admit = admit


def selected(raw): _configure(); return base.selected(raw)
def checker_task(value, row): _configure(); return base.checker_task(value, row)
def stage_task(task, output, label): _configure(); return base.stage_task(task, output, label)
def output_fields(tokens, reply, elapsed): _configure(); return base.output_fields(tokens, reply, elapsed)
def validate_pins(*args, **kwargs): _configure(); return base.validate_pins(*args, **kwargs)
def update(*args, **kwargs): _configure(); return base.update(*args, **kwargs)
def admit(a):
    _configure()
    chosen, packet = selected(a.input.read_bytes())
    parent = json.loads(Path(a.base_admission).read_bytes())
    if parent.get('kind') != 'multiexample_structural_fullmodule_probe':
        raise ValueError('Exact prior multi-example admission required')
    expected = {
        'input_sha256': base.INPUT_SHA,
        'policy_checkpoint_sha256': base.POLICY_SHA,
        'lineage_checkpoint_sha256': base.lineage.CHILD_SHA,
    }
    for key, value in expected.items():
        if parent.get(key) != value:
            raise ValueError(f'Parent admission pin changed: {key}')
    tasks = {str(i): checker_task(packet, chosen[i][0]) for i in (*TRAIN_ROWS, *EVAL_ROWS)}
    return dict(schema=1, kind='multiexample_4train_structural_fullmodule_probe',
        budget=BUDGET, rows={'train': list(TRAIN_ROWS), 'eval': list(EVAL_ROWS)},
        task_ids={str(i): ROW_IDS[i] for i in (*TRAIN_ROWS, *EVAL_ROWS)},
        encodings={str(i): chosen[i][1] for i in (*TRAIN_ROWS, *EVAL_ROWS)},
        checker_tasks=tasks,
        packet_splits={str(i): chosen[i][0]['split'] for i in (*TRAIN_ROWS, *EVAL_ROWS)},
        lineage_admission_sha256=parent['lineage_admission_sha256'],
        input_sha256=base.INPUT_SHA,
        lineage_checkpoint_sha256=parent['lineage_checkpoint_sha256'],
        policy_checkpoint_sha256=parent['policy_checkpoint_sha256'],
        source_sha256=base.sources(), training_authorized=True,
        protected_outputs_never_train=True, train_only=False, gate_claim=False,
        generalization_claim=False, proof_claim=False, tlc_claim=False,
        nonvacuity_claim=False,
        base_admission_sha256=hashlib.sha256(Path(a.base_admission).read_bytes()).hexdigest())
def worker(a): _configure(); return base.worker(a)


def main():
    _configure()
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode', choices=('admit', 'worker'))
    for n in (*base.lineage.PATHS, 'output'):
        p.add_argument('--' + n.replace('_', '-'), type=Path, required=True)
    p.add_argument('--base-admission', type=Path, required=True)
    p.add_argument('--lineage-checkpoint', type=Path, required=True)
    p.add_argument('--expected-input-sha256', required=True)
    p.add_argument('--admission', type=Path)
    a = p.parse_args()
    if a.mode == 'admit':
        if a.output.exists(): raise ValueError('Admission output must not exist')
        base.dump(a.output, admit(a))
    else:
        if a.admission is None: p.error('--admission required')
        print(json.dumps(worker(a)))


if __name__ == '__main__':
    main()
