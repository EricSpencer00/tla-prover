"""Prompt-grounded schema SFT for the full-module TLA+ contract.

This diagnostic changes the training signal after broad clean SFT changed
adapter tensors without changing either protected generation.  It keeps the
same clean W4 source partition and exact parent, but upweights target tokens
that realize identifiers explicitly required by each prompt.  The identifiers
are extracted from the prompt, while the target response remains the immutable
clean reference.  No protected target, generated feedback, replay negative,
or verifier label enters training.
"""

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import proof_fullmodule_broad_clean_sft_train as base


PACKET_SHA = base.PACKET_SHA
PARENT_SHA = base.PARENT_SHA
TRAIN = base.TRAIN
VALID = base.VALID
PROTECTED = base.PROTECTED
REFERENCE_ROWS = base.REFERENCE_ROWS
ANCHORS = base.ANCHORS
MODULE_NAMES = base.MODULE_NAMES

BUDGET = dict(
    base.BUDGET,
    steps=48,
    lr=2e-6,
    schema_weight=8.0,
    objective='prompt_grounded_identifier_schema_sft_with_retention_anchors',
)
base.BUDGET = BUDGET
base.multi.BUDGET.update(
    max_new_tokens=BUDGET['max_new_tokens'],
    item_seconds=BUDGET['generation_seconds'],
    sany_seconds=BUDGET['sany_seconds'],
    train_only=False,
    eval_rows=list(PROTECTED),
    gate_claim=False,
    quality_claim=False,
    generalization_claim=False,
    proof_claim=False,
    tlc_claim=False,
    nonvacuity_claim=False,
)


def file_sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def prompt_schema_identifiers(prompt):
    module = re.search(r'module named ([A-Za-z_][A-Za-z0-9_]*)', prompt)
    required = re.search(
        r'=== REQUIRED IDENTIFIERS \(from the reference \.cfg\) ===\n(.*?)\n\n=== TASK ===',
        prompt, re.S)
    if not module or not required:
        raise ValueError('prompt schema block is missing')
    names = [module.group(1)]
    for line in required.group(1).splitlines():
        if ':' not in line:
            continue
        names.extend(re.findall(r'[A-Za-z_][A-Za-z0-9_]*', line.split(':', 1)[1]))
    return tuple(dict.fromkeys(names))


def find_subsequence(values, needle):
    if not needle or len(needle) > len(values):
        return []
    return [i for i in range(len(values) - len(needle) + 1)
            if values[i:i + len(needle)] == needle]


def schema_exact_chat(tokenizer, prompt, response):
    enc = base._ORIGINAL_EXACT_CHAT(tokenizer, prompt, response)
    names = prompt_schema_identifiers(prompt)
    target = enc['input_ids'][enc['prompt_tokens']:]
    weights = [1.0] * len(enc['labels'])
    hits = {}
    weighted_positions = set()
    for name in names:
        positions = set()
        # SentencePiece/BPE tokenizers often merge the leading space with the
        # first identifier token.  Search the plain and common whitespace
        # prefixed forms so the match is about exact token identity rather
        # than an accidental boundary artifact.
        for spelling in (name, ' ' + name, '\n' + name, '\t' + name):
            ids = tokenizer.encode(spelling, add_special_tokens=False)
            for start in find_subsequence(target, ids):
                positions.update(range(start, start + len(ids)))
        hits[name] = len(positions)
        for position in positions:
            weighted_positions.add(enc['prompt_tokens'] + position)
    for position in weighted_positions:
        weights[position] = BUDGET['schema_weight']
    enc['schema_identifiers'] = list(names)
    enc['schema_identifier_hits'] = hits
    enc['schema_weights'] = weights
    enc['schema_weighted_tokens'] = len(weighted_positions)
    return enc


def schema_teacher_loss(net, enc, device='cuda', context=None):
    import torch
    import torch.nn.functional as F

    context = context or (lambda: torch.autocast('cuda', dtype=torch.bfloat16))
    ids = torch.tensor([enc['input_ids']], device=device)
    labels = torch.tensor([enc['labels']], device=device)
    with context():
        result = net(input_ids=ids, attention_mask=torch.ones_like(ids),
                     labels=None, use_cache=False)
    logits = result.logits[:, :-1, :].float()
    targets = labels[:, 1:]
    mask = targets.ne(-100)
    if not bool(mask.any()):
        raise ValueError('empty response target')
    flat = F.cross_entropy(logits[mask], targets[mask], reduction='none')
    weights = torch.tensor(enc['schema_weights'][1:], device=device, dtype=torch.float32)
    selected_weights = weights[mask.reshape(-1)]
    mass = selected_weights.sum()
    if not bool(torch.isfinite(mass)) or float(mass) <= 0:
        raise ValueError('invalid schema target mass')
    loss = (flat * selected_weights).sum() / mass
    top1 = (logits.argmax(-1)[mask] == targets[mask]).float().mean()
    return loss, dict(
        loss=float(loss.detach()),
        target_top1=float(top1.detach()),
        target_tokens=int(mask.sum()),
        schema_weighted_tokens=enc['schema_weighted_tokens'],
        schema_target_mass=float(mass.detach()),
    )


def install_hooks():
    if not hasattr(base, '_ORIGINAL_EXACT_CHAT'):
        base._ORIGINAL_EXACT_CHAT = base.exact_chat
    base.exact_chat = schema_exact_chat
    base.common.teacher_loss = schema_teacher_loss


def prepare(args):
    base.prepare(args)
    manifest_path = args.output / 'manifest.json'
    manifest = json.loads(manifest_path.read_text())
    manifest['schema_supervision'] = dict(
        prompt_required_identifiers=True,
        token_match='exact tokenizer subsequences in clean response target',
        schema_weight=BUDGET['schema_weight'],
        protected_targets_never_train=True,
        generated_feedback_loaded=False,
        replay_negatives_loaded=False,
    )
    dump(manifest_path, manifest)
    print(json.dumps(dict(
        prepared=len(manifest['references']),
        train=len(TRAIN),
        validation=len(VALID),
        manifest_sha256=file_sha(manifest_path),
    )))


def preflight(args):
    install_hooks()
    base.preflight(args)
    value = json.loads(args.output.read_text())
    packet = json.loads(args.packet.read_bytes())
    schema_records = []
    for row in REFERENCE_ROWS:
        source = packet['rows'][row]
        enc = schema_exact_chat(args.tokenizer_for_schema, source['prompt'], source['response'])
        schema_records.append(dict(
            row=row,
            train=row in TRAIN,
            validation=row in VALID,
            anchor=row in ANCHORS,
            identifiers=enc['schema_identifiers'],
            identifier_hits=enc['schema_identifier_hits'],
            weighted_tokens=enc['schema_weighted_tokens'],
        ))
    value['kind'] = 'fullmodule_prompt_grounded_schema_cpu_preflight_v1'
    value['schema_records'] = schema_records
    missing = [dict(row=record['row'], identifiers=[name for name, count in
               record['identifier_hits'].items() if not count]) for record in schema_records
               if any(count == 0 for count in record['identifier_hits'].values())]
    value['schema_all_references_contain_required_identifiers'] = not missing
    value['schema_missing_required_identifiers'] = missing
    value['schema_weight'] = BUDGET['schema_weight']
    dump(args.output, value)
    print(json.dumps(dict(
        preflight='pass',
        references=len(schema_records),
        schema_records=len(schema_records),
        preflight_sha256=file_sha(args.output),
    )))


def train(args):
    install_hooks()
    base.train(args)
    receipt_path = args.output / 'receipt.json'
    receipt = json.loads(receipt_path.read_text())
    receipt['schema_supervision'] = dict(
        prompt_required_identifiers=True,
        token_match='exact tokenizer subsequences in clean response target',
        schema_weight=BUDGET['schema_weight'],
        generated_feedback_used_for_training=False,
        replay_negatives_loaded=False,
    )
    dump(receipt_path, receipt)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=('prepare', 'preflight', 'train'))
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--jar', type=Path, required=True)
    parser.add_argument('--java', default='java')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--manifest', type=Path)
    parser.add_argument('--manifest-sha256')
    parser.add_argument('--preflight', type=Path)
    parser.add_argument('--preflight-sha256')
    parser.add_argument('--checkpoint', type=Path)
    parser.add_argument('--model', type=Path, required=True)
    args = parser.parse_args()
    if args.mode == 'prepare':
        prepare(args)
    elif args.mode == 'preflight':
        if not args.manifest or not args.manifest_sha256:
            parser.error('preflight requires manifest and manifest-sha256')
        import transformers
        args.tokenizer_for_schema = transformers.AutoTokenizer.from_pretrained(
            args.model, local_files_only=True)
        preflight(args)
    else:
        if not all((args.manifest, args.manifest_sha256, args.preflight,
                    args.preflight_sha256, args.checkpoint)):
            parser.error('train requires manifest, preflight, and checkpoint')
        train(args)
