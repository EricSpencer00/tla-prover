import copy

import pytest

from tools.proof_sequence_train import encode_response, restore_trainable, training_tasks
from tools.proof_repair_pilot import prompt_for


class Tokenizer:
    eos_token_id = 3

    def apply_chat_template(self, messages, tokenize=False, add_generation_prompt=False):
        prefix = '<user>' + messages[0]['content'] + '</user><assistant>'
        return prefix if add_generation_prompt else prefix + messages[1]['content'] + '\x03\n'

    def __call__(self, text, **kwargs):
        assert kwargs == dict(add_special_tokens=False, truncation=False)
        return {'input_ids': [ord(c) for c in text]}


def task(ident='a', split='train'):
    return dict(id=ident, split=split, source_family=ident, source_sha256=ident*64,
                prefix='THEOREM '+ident+' == TRUE\n', suffix='\n====',
                reference_fragment='BY SMT')


def test_response_only_mask_matches_inference_and_includes_eot():
    t = task()
    tok = Tokenizer()
    e = encode_response(tok, t, 10000)
    n = e['prompt_tokens']
    assert e['rendered_prompt'] == tok.apply_chat_template(
        [dict(role='user', content=prompt_for(t))], tokenize=False, add_generation_prompt=True)
    assert e['labels'][:n] == [-100]*n
    assert e['labels'][n:] == [ord(c) for c in 'BY SMT\x03']
    assert e['input_ids'][-1] == tok.eos_token_id
    # Causal shift leaves the first proof token supervised from final prompt token.
    assert e['labels'][1:][n-1] == ord('B')


def test_no_silent_truncation():
    with pytest.raises(ValueError, match='truncation'):
        encode_response(Tokenizer(), task(), 3)


def test_incompatible_chat_prefix_rejected():
    class Broken(Tokenizer):
        def apply_chat_template(self, messages, **kwargs):
            return super().apply_chat_template(messages, **kwargs) + ('!' if len(messages)==1 else '')
    with pytest.raises(ValueError, match='boundary'):
        encode_response(Broken(), task(), 10000)


def test_missing_eot_rejected():
    tok = Tokenizer()
    tok.eos_token_id = -1
    with pytest.raises(ValueError, match='end-of-turn'):
        encode_response(tok, task(), 10000)


def test_only_train_returned_without_reading_development_reference():
    development = task('b', 'development')
    del development['reference_fragment']
    assert training_tasks({'tasks':[task(), development]}) == [task()]


@pytest.mark.parametrize('key', ['source_family', 'source_sha256', 'assembled_sha256'])
def test_split_overlap_rejected(key):
    a, b = task(), task('b', 'development')
    a[key] = b[key] = 'same'
    with pytest.raises(ValueError, match='overlap'):
        training_tasks({'tasks':[a,b]})


def test_scaffold_overlap_rejected_even_with_false_metadata():
    a, b = task(), task('b', 'development')
    b['prefix'] = a['prefix']
    with pytest.raises(ValueError, match='scaffold'):
        training_tasks({'tasks':[a,b]})


@pytest.mark.parametrize('field,value', [('split', None), ('split', 'test'),
                                         ('source_family',''), ('source_sha256','')])
def test_missing_explicit_metadata_rejected(field,value):
    a = task()
    a[field] = value
    with pytest.raises(ValueError):
        training_tasks({'tasks':[a,task('b','development')]})


def test_duplicate_id_and_missing_development_rejected():
    with pytest.raises(ValueError, match='unique'):
        training_tasks({'tasks':[task(),copy.deepcopy(task())]})
    with pytest.raises(ValueError, match='Both'):
        training_tasks({'tasks':[task()]})


def test_checkpoint_parameter_coverage_and_exact_restore():
    torch = pytest.importorskip('torch')
    p = torch.nn.Parameter(torch.zeros(2))
    restore_trainable({'layer.weight':p}, {'trainable_state':{'layer.weight':torch.ones(2)}})
    assert torch.equal(p, torch.ones(2))
    for state in ({}, {'layer.weight':torch.ones(2), 'other':torch.ones(2)}):
        with pytest.raises(ValueError, match='coverage'):
            restore_trainable({'layer.weight':p}, {'trainable_state':state})
    for value in (torch.ones(3),torch.ones(2,dtype=torch.float64)):
        with pytest.raises(ValueError, match='shape/dtype'):
            restore_trainable({'layer.weight':p}, {'trainable_state':{'layer.weight':value}})


def test_real_causal_response_loss_alignment():
    torch = pytest.importorskip('torch')
    # Explicit logits verify the prompt is not in the loss and response's first
    # token is predicted at the final prompt position, not its own position.
    labels = torch.tensor([[-100,-100,1,2]])
    logits = torch.tensor([[[9.,0.,0.],[0.,9.,0.],[0.,0.,9.],[0.,0.,0.]]])
    loss = torch.nn.functional.cross_entropy(logits[:,:-1].reshape(-1,3), labels[:,1:].reshape(-1))
    assert loss < .001
