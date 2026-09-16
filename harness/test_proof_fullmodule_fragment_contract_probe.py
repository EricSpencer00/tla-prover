from tools import proof_fullmodule_fragment_contract_probe as probe


def test_split_preserves_exact_header_and_body():
    source = "---- MODULE Demo ----\nEXTENDS Naturals\n====\n"
    split = probe.split_source(source)
    assert split["header"] == "---- MODULE Demo ----\n"
    assert split["body"] == "EXTENDS Naturals\n====\n"
    assert split["module_name"] == "Demo"


def test_fragment_contract_is_strict_and_nonrepairing():
    header = "---- MODULE Demo ----\n"
    body = "EXTENDS Naturals\n====\n"
    assert probe.validate_fragment(header, body, "Demo")["accepted"]
    assert not probe.validate_fragment("MODULE Demo\n", body, "Demo")["accepted"]
    assert not probe.validate_fragment(header, "SEGMENT: 0\n" + body, "Demo")["accepted"]
    assert not probe.validate_fragment(header, body + "EXTRA\n", "Demo")["accepted"]


def test_reference_assembly_is_not_a_model_or_quality_claim(monkeypatch):
    assert probe.PROTECTED == (47, 107)
    assert probe.PARENT_SHA.startswith("87489e47")
