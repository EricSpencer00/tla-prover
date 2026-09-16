"""Admission and collection contract for an expanded full-module SANY corpus.

This is intentionally a separate branch from the two-row feedback experiment.
It pins six development rows (45, 46, 50--53) from the immutable TRAIN169
packet and keeps rows 47 and 107 protected evaluation rows.  The module does
not run a model or authorize training; an authenticated collector must consume
this admission before writing feedback records.
"""
import json
from pathlib import Path

from tools import proof_fullmodule_learning_train as lineage
from tools import proof_fullmodule_multiexample_probe as multi

ROOT = Path(__file__).resolve().parents[1]
INPUT_SHA = multi.INPUT_SHA
BASE_KIND = 'multiexample_4train_structural_fullmodule_probe'
DEV_ROWS = (45, 46, 50, 51, 52, 53)
EVAL_ROWS = (47, 107)
ALL_ROWS = DEV_ROWS + EVAL_ROWS

ROW_IDS = {
    45: 'w4-fullmodule:w4opus::d18-m9-p1-t2',
    46: 'w4-fullmodule:w4opus::d13-m1-p5-t1',
    47: 'w4-fullmodule:w4opus::d2-m7-p4-t2',
    50: 'w4-fullmodule:w4opus::d10-m2-p0-t3',
    51: 'w4-fullmodule:w4opus::d4-m2-p0-t1',
    52: 'w4-fullmodule:w4opus::d19-m7-p2-t1',
    53: 'w4-fullmodule:w4opus::d12-m7-p3-t1',
    107: 'w4-fullmodule:w4opus::d3-m0-p0-t0',
}
PROMPT_SHAS = {
    45: 'b64c4d644820db3e58bbfd73939d2bd152d1d595d60c8966a2ec301e55842e4d',
    46: '9fd26650efd01caf164643adf86025bcfa79f659b3f3c71073ad29c27597f934',
    47: '32eb750d7db375df72e8e93d929ac3e5c7a365d50a915202c62db6e3d675877f',
    50: '6a581ec51f08d1b40e9b0160b4412c934a3eb4a670c5728fe71a0de6c4f235cb',
    51: '6949856dd558d1fa73db7eb72415b4243e437fb3323221fb01579ff912556474',
    52: '61e7967c757f2c2fb6a3c85f8bfd7b7937d10becf5e1b58843cf7929f9e22132',
    53: '133e766fd2cca1b0b52b3013341a54c8b35bfde4ea6174d14fe43a9b4de00c86',
    107: '388d75fc27a48d38ccb3fd0258a72ddfd1b9dbb0852b0b058057521e8eaafb51',
}
RESPONSE_SHAS = {
    45: 'bad6c0dff5965a7363ecf1abf1a6a3faab714ad81cceff6c88b223cd62dac9fb',
    46: '9f436f4463f97528db6c948e1d0befd03bd20d18cdb14065d53af6d40827872c',
    47: '36c548d2a475c0d086ddf0340f927b36002699ce86e955d702e061324ad2f07c',
    50: '4eb9d23b701851e2039a5d2c00696cd9b618d68204778295ba38187c3ed30378',
    51: 'ae56c12d774b6daa7440e132fc988e8d057c3a10590a97cec75898baab7e2a22',
    52: '769f844aaa3a81ab2a77b59922b84824d678c071468f8ab3b96bd5be021e7132',
    53: '53db414f719adaeb58a9890f7164294c44d16721963b31b855ad648be147d66c',
    107: '5f6b169dc010369d4e6f65b7766b7961e44a4df15790988c5763861a06e3e853',
}

BUDGET = dict(updates=128, lr=1e-5, item_seconds=45, sany_seconds=30,
              response_only=True, final_layer_only=True,
              dev_rows=list(DEV_ROWS), eval_rows=list(EVAL_ROWS),
              feedback_records=6, training_authorized=False,
              gate_claim=False, generalization_claim=False, proof_claim=False,
              tlc_claim=False, nonvacuity_claim=False)


def load(path):
    return json.loads(Path(path).read_bytes())


def selected(raw):
    if lineage.helpers.sha(raw) != INPUT_SHA:
        raise ValueError('Exact immutable TRAIN169 packet required')
    packet = json.loads(raw)
    rows = lineage.packet.validate_training_packet(packet)
    selected_rows = {}
    for i in ALL_ROWS:
        row, enc = rows[i], packet['encodings'][i]
        if (row['id'], row['prompt_sha256'], row['response_sha256']) != (
                ROW_IDS[i], PROMPT_SHAS[i], RESPONSE_SHAS[i]):
            raise ValueError(f'pinned corpus row {i} changed')
        if row['split'] != 'train':
            raise ValueError(f'packet row {i} changed split')
        selected_rows[i] = (row, enc)
    return selected_rows, packet


def admit(input_path, base_admission_path):
    """Create a non-training admission bound to the audited four-row parent."""
    selected(Path(input_path).read_bytes())
    parent = load(base_admission_path)
    if parent.get('kind') != BASE_KIND:
        raise ValueError('exact authenticated four-row admission required')
    if tuple(parent.get('rows', {}).get('train', ())) != (42, 43, 44, 49):
        raise ValueError('four-row training partition changed')
    if tuple(parent.get('rows', {}).get('eval', ())) != EVAL_ROWS:
        raise ValueError('protected eval partition changed')
    if parent.get('input_sha256') != INPUT_SHA:
        raise ValueError('base packet pin changed')
    return dict(schema=1, kind='sany_feedback_corpus_scaffold', budget=BUDGET,
        dev_rows=list(DEV_ROWS), eval_rows=list(EVAL_ROWS),
        row_ids={str(i): ROW_IDS[i] for i in ALL_ROWS},
        prompt_shas={str(i): PROMPT_SHAS[i] for i in ALL_ROWS},
        response_shas={str(i): RESPONSE_SHAS[i] for i in ALL_ROWS},
        input_sha256=INPUT_SHA,
        base_admission_sha256=lineage.helpers.file_sha(Path(base_admission_path)),
        feedback_training_authorized=False, eval_rows_never_train=True,
        eval_rows_never_decoded=True, target_text_not_in_feedback=True,
        gate_claim=False, generalization_claim=False, proof_claim=False,
        tlc_claim=False, nonvacuity_claim=False,
        blocker='requires six authenticated development SANY feedback records')


def validate_feedback(record):
    """Validate one collector record without admitting a target answer."""
    if not isinstance(record, dict) or set(record) != {'row', 'draft', 'diagnostic', 'draft_sha256'}:
        raise ValueError('feedback record must contain only row,draft,diagnostic,draft_sha256')
    i = record['row']
    if i not in DEV_ROWS:
        raise ValueError('feedback record is outside development rows')
    if not isinstance(record['draft'], str) or not record['draft']:
        raise ValueError('draft required')
    if not isinstance(record['diagnostic'], str) or not record['diagnostic']:
        raise ValueError('authenticated SANY diagnostic required')
    if lineage.helpers.sha(record['draft'].encode()) != record['draft_sha256']:
        raise ValueError('draft hash changed')
    if 'sany' not in record['diagnostic'].lower() and 'error' not in record['diagnostic'].lower():
        raise ValueError('diagnostic is not visibly a SANY/error report')
    return True


def load_feedback(path):
    """Authenticate an append-only six-record collection artifact."""
    root = Path(path)
    receipt = load(root / 'receipt.json')
    if receipt.get('kind') != 'sany_feedback_collection' or receipt.get('complete') is not True:
        raise ValueError('completed SANY feedback collection required')
    stream = root / 'feedback.jsonl'
    if lineage.helpers.file_sha(stream) != receipt.get('feedback_sha256'):
        raise ValueError('feedback artifact hash changed')
    records = [json.loads(line) for line in stream.read_text().splitlines() if line.strip()]
    if [r.get('row') for r in records] != list(DEV_ROWS):
        raise ValueError('exact ordered six-row development feedback records required')
    for record in records:
        validate_feedback(record)
    if receipt.get('dev_rows') != list(DEV_ROWS) or receipt.get('eval_rows') != list(EVAL_ROWS):
        raise ValueError('collection partition changed')
    if receipt.get('eval_rows_never_train') is not True or receipt.get('eval_rows_never_decoded') is not True:
        raise ValueError('collection does not attest eval isolation')
    return receipt, {record['row']: record for record in records}


if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument('mode', choices=('admit',))
    p.add_argument('--input', type=Path, required=True)
    p.add_argument('--base-admission', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    if a.output.exists():
        raise ValueError('append-only output already exists')
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(admit(a.input, a.base_admission), indent=2) + '\n')
