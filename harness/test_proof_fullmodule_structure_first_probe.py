"""Lightweight tests for the CPU-only structure-first decomposition."""

from tools import proof_fullmodule_structure_first_probe as probe
from tools import proof_fullmodule_structure_first_sft_train as worker


def test_decompose_is_lossless_and_ignores_indented_let_bindings():
    text = (
        '---- MODULE Demo ----\n'
        'EXTENDS Naturals\n'
        'CONSTANT K\n'
        '\n'
        'Init ==\n'
        '    LET local == 1 IN local = 1\n'
        '\n'
        'Next(x) == x + 1\n'
        '====\n'
    )
    structure = probe.decompose(text)
    assert structure['module_name'] == 'Demo'
    assert structure['operator_count'] == 2
    assert [part['operator_name'] for part in structure['parts']
            if part['kind'] == 'operator'] == ['Init', 'Next']
    assert structure['reconstruction_exact'] is True
    assert structure['reconstructed_sha256'] == probe.sha(text.encode())
    assert structure['largest_operator_char_count'] < len(text)


def test_decompose_keeps_comments_and_footer_bytes_exact():
    text = (
        '\n'
        '---------------- MODULE Demo2 ----------------\n'
        '(* declaration comment *)\n'
        '\n'
        'Spec == TRUE\n'
        '\n'
        '\\* trailing comment\n'
        '========\n'
        '\n'
    )
    structure = probe.decompose(text)
    assert structure['module_name'] == 'Demo2'
    assert structure['parts'][-1]['kind'] == 'footer'
    assert ''.join(text[p['start_char']:p['end_char']]
                   for p in structure['parts']) == text


def test_structure_first_plan_contract_and_forced_eos_boundary():
    structure = {
        'parts': [
            {'kind': 'header', 'id': 'header'},
            {'kind': 'declarations', 'id': 'declarations'},
            {'kind': 'operator', 'id': 'operator-000-Init', 'index': 0},
            {'kind': 'footer', 'id': 'footer'},
        ]
    }
    plan = worker.plan_text('Demo', structure)
    parsed = worker.parse_plan(plan, 'Demo')
    assert [part['id'] for part in parsed] == [
        'header', 'declarations', 'operator-000-Init', 'footer']
    try:
        worker.parse_plan('---- MODULE Demo ----\n====\n', 'Demo')
    except ValueError as exc:
        assert str(exc) == 'plan envelope mismatch'
    else:
        raise AssertionError('raw TLA must not satisfy the plan envelope')

    class InputIds:
        def __init__(self, values): self.values = values
        def tolist(self): return [self.values]

    class Scores:
        def __init__(self): self.assignments = []
        def __setitem__(self, key, value): self.assignments.append((key, value))

    processor = worker.ForceEosAfterPlan([4, 5], 9, prompt_tokens=2)
    scores = Scores()
    processor(InputIds([1, 2, 3, 4, 5]), scores)
    assert scores.assignments == [((0, slice(None)), float('-inf')), ((0, 9), 0.0)]
    assert worker.PLAN_PREFIX == 'STRUCTURE-FIRST PLAN\nMODULE: '
    assert worker.PLAN_STOP == 'END PLAN\n'
