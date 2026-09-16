"""Fail-closed audit checks for the GPU/local-verifier handoff (no GPU needed)."""
import copy
import json
from types import SimpleNamespace

import pytest

from tools.proof_offline_eval import sha, validate_generations, validate_prompts, verify


def fixture():
    prompt = 'Immutable theorem\n<PROOF_HOLE>'
    tasks = [dict(id=key, prompt=prompt, prompt_sha256=sha(prompt.encode())) for key in ('a', 'b')]
    data = dict(split='development', reference_fragments_exported=False, tasks=tasks)
    encoded = json.dumps(data).encode()
    config = dict(prompts_sha256=sha(encoded), requested_task_ids=['a', 'b'], max_new_tokens=512)
    rendered, reply = 'USER\n'+prompt+'\nASSISTANT', 'BY SMT'
    row = dict(id='a', prompt=prompt, prompt_sha256=sha(prompt.encode()),
               rendered_prompt=rendered, rendered_prompt_sha256=sha(rendered.encode()),
               raw_reply=reply, raw_reply_sha256=sha(reply.encode()),
               token_ids=[3, 4], output_tokens=2, input_token_ids=[1, 2, 3], input_tokens=3,
               hit_token_limit=False)
    return encoded, data, config, [row]


def test_valid_partial_and_complete_generations():
    args = fixture()
    validate_generations(*args)
    second = dict(args[3][0], id='b')
    validate_generations(*args[:3], args[3]+[second])
    validate_generations(*args[:3], [])


@pytest.mark.parametrize('mutation', ['duplicate', 'hash', 'answer', 'empty', 'contract'])
def test_prompt_export_rejects_invalid_data(mutation):
    _, data, _, _ = fixture()
    if mutation == 'duplicate':
        data['tasks'].append(copy.deepcopy(data['tasks'][0]))
    elif mutation == 'hash':
        data['tasks'][0]['prompt'] += 'changed'
    elif mutation == 'answer':
        data['tasks'][0]['reference_fragment'] = 'BY SMT'
    elif mutation == 'empty':
        data['tasks'] = []
    else:
        data['reference_fragments_exported'] = True
    with pytest.raises(ValueError):
        validate_prompts(data)


@pytest.mark.parametrize('field,value', [
    ('prompts_sha256', 'bad'), ('requested_task_ids', ['a']), ('max_new_tokens', 1024),
])
def test_generation_config_requires_matching_file_population_and_budget(field, value):
    args = fixture()
    args[2][field] = value
    with pytest.raises(ValueError):
        validate_generations(*args)


@pytest.mark.parametrize('field,value', [
    ('id', 'unknown'), ('prompt', 'changed'), ('prompt_sha256', 'bad'),
    ('raw_reply', 'CHANGED'), ('rendered_prompt', 'CHANGED'),
    ('token_ids', [1]), ('input_token_ids', [1]), ('output_tokens', True),
    ('input_tokens', -1), ('token_ids', [-1, 0]), ('hit_token_limit', True),
])
def test_generation_row_tampering_rejected(field, value):
    args = fixture()
    args[3][0][field] = value
    with pytest.raises(ValueError):
        validate_generations(*args)


def test_duplicate_generation_rejected():
    args = fixture()
    args[3].append(copy.deepcopy(args[3][0]))
    with pytest.raises(ValueError, match='duplicate'):
        validate_generations(*args)


def test_skipping_interior_task_rejected():
    args = fixture()
    args[3][0]['id'] = 'b'
    with pytest.raises(ValueError, match='order'):
        validate_generations(*args)


def test_rendered_prompt_must_retain_exported_content():
    args = fixture()
    args[3][0].update(rendered_prompt='different', rendered_prompt_sha256=sha(b'different'))
    with pytest.raises(ValueError, match='original user content'):
        validate_generations(*args)


def test_verify_rejects_changed_manifest_before_writing_results(tmp_path):
    _, data, _, _ = fixture()
    data['manifest_sha256'] = sha(b'original manifest')
    prompts = tmp_path/'prompts.json'
    prompts.write_text(json.dumps(data))
    manifest = tmp_path/'manifest.json'
    manifest.write_text('{}')
    with pytest.raises(ValueError, match='manifest hash mismatch'):
        verify(SimpleNamespace(prompts=prompts, manifest=manifest, output=tmp_path))
    assert not (tmp_path/'rows.jsonl').exists()


def test_output_token_limit_is_exact():
    args = fixture()
    args[3][0].update(token_ids=[1]*512, output_tokens=512, hit_token_limit=True)
    validate_generations(*args)
    args[3][0].update(token_ids=[1]*513, output_tokens=513, hit_token_limit=False)
    with pytest.raises(ValueError, match='budget'):
        validate_generations(*args)
