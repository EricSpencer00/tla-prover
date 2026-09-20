import pytest

from tools.proof_syntax_structure_diagnostic import structural_spans


def test_structural_spans_preserve_complete_definitions():
    text = "- MODULE M -\nEXTENDS Integers\n\nVARIABLES x\n\nInit == x = 0\n\nNext == x' = x + 1\n\n====\n"
    spans = structural_spans(text)
    assert [span["kind"] for span in spans] == ["EXTENDS", "VARIABLES", "Init", "Next", "===="]
    assert spans[2]["text"] == "Init == x = 0\n\n"


def test_empty_or_header_only_has_no_false_spans():
    assert structural_spans("- MODULE M -\n\n") == []


def test_structural_spans_rejects_no_input_only_at_callers():
    assert structural_spans("VARIABLES x\n") == [{"kind": "VARIABLES", "text": "VARIABLES x\n"}]
