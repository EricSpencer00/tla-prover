"""Protected-only raised-cap replay evaluation.

This is an inference-only follow-up to the mixed replay repair.  It changes
only the generation budget, keeps rows 47 and 107 protected from training, and
records exact SANY diagnostics for the candidate and immutable references.
"""
import argparse
import json
from pathlib import Path

from tools import proof_fullmodule_sany_feedback_current_child as base
from tools import proof_fullmodule_sany_feedback_repair_probe as repair
from tools import proof_fullmodule_learning_train as lineage
from tools import proof_fullmodule_multiexample_probe as multi


EVAL_ROWS = (47, 107)
EXPECTED_CANDIDATE_SHA = '1d4fce896e0d55b10cf3f6943df58fabd6aeebb3649c98822dc0385b36fd32c4'


def load(path):
    return json.loads(Path(path).read_bytes())


def dump(path, value):
    lineage.helpers.dump(Path(path), value)


def run(a):
    import torch
    import transformers

    if lineage.helpers.sha(a.candidate.read_bytes()) != EXPECTED_CANDIDATE_SHA:
        raise ValueError('Exact mixed-replay candidate checkpoint required')
    chosen, packet = base.selected(a.input.read_bytes())
    a.output.mkdir(parents=True, exist_ok=False)
    tasks = {
        i: multi.stage_task(multi.checker_task(packet, chosen[i][0]), a.output, str(i))
        for i in EVAL_ROWS
    }
    current = multi.sany.identity(list(tasks.values()))
    tokenizer = transformers.AutoTokenizer.from_pretrained(
        str(a.model_path), local_files_only=True)
    net = lineage.helpers.load_policy(str(a.model_path))
    saved = torch.load(a.candidate, map_location='cpu', weights_only=False)
    lineage.helpers.restore_policy(
        net, saved, lineage.helpers.model_files(a.model_path))
    prior = base.eval_feedback(a.eval_context, a.child_checkpoint)
    row47 = repair._prompt_only(tokenizer, repair.eval_feedback_prompt(
        chosen[47][0]['prompt'], prior['draft'], prior['diagnostic']))
    row107 = repair._prompt_only(tokenizer, chosen[107][0]['prompt'])

    old_budget = dict(multi.BUDGET)
    multi.BUDGET['max_new_tokens'] = a.max_new_tokens
    multi.BUDGET['item_seconds'] = a.item_seconds
    try:
        posts = {
            '47': multi.decode(
                net, tokenizer, row47,
                forced_prefix='---- MODULE W4Od2m7p4t2 ----\n'),
            '107': multi.decode(
                net, tokenizer, row107,
                forced_prefix='---- MODULE W4Od3m0p0t0 ----\n'),
        }
    finally:
        multi.BUDGET.clear()
        multi.BUDGET.update(old_budget)

    candidates = {}
    for i in EVAL_ROWS:
        post = posts[str(i)]
        candidates[str(i)] = (
            multi.sany.check(
                tasks[i], post['raw_reply'],
                a.output / 'sany_candidate' / str(i), current,
                timeout=a.sany_seconds)
            if post['finish_reason'] == 'eos' else None
        )
    references = {
        str(i): multi.sany.check(
            tasks[i], chosen[i][0]['response'],
            a.output / 'sany_reference' / str(i), current,
            timeout=a.sany_seconds)
        for i in EVAL_ROWS
    }
    receipt = dict(
        schema=1,
        kind='sany_replay_long_eval',
        complete=True,
        candidate_checkpoint_sha256=lineage.helpers.sha(a.candidate.read_bytes()),
        input_sha256=base.PACKET_SHA,
        child_checkpoint_sha256=base.CURRENT_CHILD_SHA,
        eval_rows=list(EVAL_ROWS),
        max_new_tokens=a.max_new_tokens,
        item_seconds=a.item_seconds,
        post=posts,
        candidate=candidates,
        reference=references,
        candidate_sany_pass={
            str(i): bool(candidates[str(i)] and candidates[str(i)].get('sany') == 1)
            for i in EVAL_ROWS
        },
        reference_sany_pass={
            str(i): references[str(i)].get('sany') == 1 for i in EVAL_ROWS
        },
        training_authorized=False,
        gate_claim=False,
        quality_claim=False,
        proof_claim=False,
        generalization_claim=False,
        tlc_claim=False,
        nonvacuity_claim=False,
    )
    dump(a.output / 'receipt.json', receipt)
    print(json.dumps(receipt, sort_keys=True))


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--input', type=Path, required=True)
    p.add_argument('--candidate', type=Path, required=True)
    p.add_argument('--child-checkpoint', type=Path, required=True)
    p.add_argument('--eval-context', type=Path, required=True)
    p.add_argument('--model-path', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--max-new-tokens', type=int, default=2048)
    p.add_argument('--item-seconds', type=int, default=60)
    p.add_argument('--sany-seconds', type=int, default=30)
    args = p.parse_args()
    run(args)


if __name__ == '__main__':
    main()
