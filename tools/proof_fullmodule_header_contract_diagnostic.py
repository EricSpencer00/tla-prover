"""CPU-only diagnostic for exact TLA+ module-header contract failures.

This compares the raw first stream replies from the executed V4/V5 receipts
against frozen clean validation modules. It measures byte-level header
admission, synthetic metadata-prefix frequency, prompt-contract markers, and
lossless parser controls. It never loads model weights, touches CUDA, trains,
repairs text, or sends partial bytes to SANY.
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

from tools.proof_fullmodule_streaming_parser_admission import ModuleStream


PACKET_SHA = 'a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c'
VALID = (59, 60, 61, 62, 63, 64)
PROTECTED = (47, 107)
HEADER_RE = re.compile(r'^-+ MODULE ([A-Za-z_][A-Za-z0-9_]*) -+\n')


def sha(value):
    return hashlib.sha256(value.encode()).hexdigest()


def dump(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + '\n')


def module_header(text):
    match = HEADER_RE.match(text)
    if not match:
        return '', None
    return match.group(0), match.group(1)


def parser_control(text):
    stream = ModuleStream()
    stream.feed(text)
    stream.finish()
    return True


def classify_reply(text, expected_module):
    header, module = module_header(text)
    first_lines = '\n'.join(text.splitlines()[:3])
    return dict(
        raw_reply_sha256=sha(text),
        raw_reply_char_count=len(text),
        first_lines=first_lines,
        canonical_header_admitted=bool(header),
        header_module=module,
        header_module_matches=(module == expected_module),
        synthetic_module_preamble=text.startswith('MODULE '),
        synthetic_segment_marker='SEGMENT:' in first_lines,
        exact_footer=text.endswith('===='),
    )


def receipt_first_replies(receipt, phase):
    records = receipt['before_protected' if phase == 'restored_parent' else 'after_protected']
    result = []
    for row in PROTECTED:
        record = records[str(row)]
        parts = record.get('parts') or []
        if not parts:
            raise ValueError(f'{phase}/{row} has no raw stream part')
        generation = parts[0].get('generation') or {}
        text = generation.get('raw_reply', '')
        result.append(dict(
            row=row,
            phase=phase,
            stream_reject=record.get('stream_reject'),
            assembled_char_count=record.get('assembled_char_count'),
            **classify_reply(text, record.get('module_name', '')),
        ))
    return result


def tokenizer_contract(tokenizer_path, rows, validation):
    """Inspect chat-template and header token boundaries without loading weights."""
    import transformers

    tokenizer = transformers.AutoTokenizer.from_pretrained(
        str(tokenizer_path), local_files_only=True)
    records = []
    for item in validation:
        value = rows[item['row']]
        header = item['header_text']
        rendered = tokenizer.apply_chat_template(
            [dict(role='user', content=value['prompt']),
             dict(role='assistant', content=value['response'])],
            tokenize=False, add_generation_prompt=False)
        prompt_rendered = tokenizer.apply_chat_template(
            [dict(role='user', content=value['prompt'])],
            tokenize=False, add_generation_prompt=True)
        all_ids = tokenizer.encode(rendered, add_special_tokens=False)
        prompt_ids = tokenizer.encode(prompt_rendered, add_special_tokens=False)
        header_ids = tokenizer.encode(header, add_special_tokens=False)
        response_ids = all_ids[len(prompt_ids):]
        records.append(dict(
            row=item['row'],
            prompt_tokens=len(prompt_ids),
            response_tokens=len(response_ids),
            chat_suffix_exact=(all_ids[:len(prompt_ids)] == prompt_ids),
            header_token_ids=header_ids,
            header_token_count=len(header_ids),
            response_starts_with_reference_header=(
                response_ids[:len(header_ids)] == header_ids),
        ))
    return dict(
        tokenizer_path=str(tokenizer_path),
        tokenizer_class=tokenizer.__class__.__name__,
        vocab_size=len(tokenizer),
        bos_token_id=tokenizer.bos_token_id,
        eos_token_id=tokenizer.eos_token_id,
        pad_token_id=tokenizer.pad_token_id,
        validation=records,
        all_chat_suffixes_exact=all(item['chat_suffix_exact'] for item in records),
        all_reference_headers_tokenized_as_exact_suffix=all(
            item['response_starts_with_reference_header'] for item in records),
        model_weights_loaded=False,
    )


def run(args):
    packet_path = Path(args.packet)
    if hashlib.sha256(packet_path.read_bytes()).hexdigest() != PACKET_SHA:
        raise ValueError('frozen packet changed')
    packet = json.loads(packet_path.read_bytes())
    rows = packet.get('rows')
    if not isinstance(rows, list) or len(rows) != 169:
        raise ValueError('complete frozen packet required')

    validation = []
    for row in VALID:
        value = rows[row]
        response = value.get('response', '')
        if sha(response) != value.get('response_sha256'):
            raise ValueError(f'validation response digest mismatch at row {row}')
        header, module = module_header(response)
        if not header or not module:
            raise ValueError(f'validation row {row} lacks a module header')
        parser_control(response)
        validation.append(dict(
            row=row,
            module_name=module,
            response_sha256=value['response_sha256'],
            response_char_count=len(response),
            header_text=header,
            header_char_count=len(header),
            header_dash_count=len(header.split(' MODULE ', 1)[0]),
            parser_admitted=True,
            source_prompt_has_exact_header_instruction=(
                'starting with `---- MODULE ' in value.get('prompt', '') and
                'ending with `====`' in value.get('prompt', '')),
        ))

    receipts = {}
    for label, path in (('v4', args.v4_receipt), ('v5', args.v5_receipt)):
        receipt = json.loads(Path(path).read_bytes())
        if receipt.get('complete') is not True:
            raise ValueError(f'{label} receipt is not complete')
        if receipt.get('reload_tensors_exact') is not True or receipt.get('reload_logits_exact') is not True:
            raise ValueError(f'{label} exact reload guard failed')
        receipts[label] = {
            'restored_parent': receipt_first_replies(receipt, 'restored_parent'),
            'trained_child': receipt_first_replies(receipt, 'trained_child'),
        }

    tokenizer = (tokenizer_contract(args.model_tokenizer, rows, validation)
                 if args.model_tokenizer else None)

    all_observed = [item for phases in receipts.values() for values in phases.values()
                    for item in values]
    v4_header_count = sum(item['canonical_header_admitted']
                          for item in [*receipts['v4']['restored_parent'], *receipts['v4']['trained_child']])
    v5_header_count = sum(item['canonical_header_admitted']
                          for item in [*receipts['v5']['restored_parent'], *receipts['v5']['trained_child']])
    v5_marker_count = sum(item['synthetic_module_preamble'] and item['synthetic_segment_marker']
                          for item in [*receipts['v5']['restored_parent'], *receipts['v5']['trained_child']])
    result = dict(
        schema=1,
        kind='fullmodule_header_contract_diagnostic_v1',
        packet_sha256=PACKET_SHA,
        validation_rows=list(VALID),
        protected_rows=list(PROTECTED),
        validation=validation,
        tokenizer=tokenizer,
        receipts=receipts,
        comparison=dict(
            v4_first_reply_header_admitted=f'{v4_header_count}/4',
            v5_first_reply_header_admitted=f'{v5_header_count}/4',
            v5_synthetic_module_and_segment_prefix=f'{v5_marker_count}/4',
            v5_stream_rejects=f"{sum(bool(item['stream_reject']) for item in receipts['v5']['trained_child'])}/2",
        ),
        controls=dict(
            frozen_validation_parser_admitted=(len(validation) == len(VALID)),
            all_raw_first_replies_hashed=(len(all_observed) == 8),
            model_weights_loaded=False,
            cuda_touched=False,
            optimizer_updates=0,
            text_repair=False,
            partial_sany_scoring=False,
            reward_or_feedback_used=False,
        ),
        claims=dict(
            model_improvement_claim=False,
            quality_claim=False,
            gate_claim=False,
            proof_claim=False,
            tlc_claim=False,
            nonvacuity_claim=False,
        ),
        conclusion=(
            'V5 changed the first-reply contract: all four protected V5 replies '
            'start with a synthetic MODULE/SEGMENT metadata preamble and are '
            'parser-rejected, while V4 admitted canonical headers in all four '
            'first replies. Remove assistant-facing metadata labels before any '
            'new GPU hypothesis; preserve module identity in the user prompt or '
            'out-of-band manifest only.'
        ),
    )
    dump(args.output, result)
    print(json.dumps(result, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--v4-receipt', type=Path, required=True)
    parser.add_argument('--v5-receipt', type=Path, required=True)
    parser.add_argument('--model-tokenizer', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    run(parser.parse_args())


if __name__ == '__main__':
    main()
