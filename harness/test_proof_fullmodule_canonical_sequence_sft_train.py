from tools import proof_fullmodule_canonical_sequence_sft_train as worker


def test_target_is_one_canonical_frame_without_prefix():
    rows = {42: {"response": "---- MODULE Demo ----\nInit == TRUE\n====\n"}}
    structures = {42: {"module_name": "Demo"}}
    target = worker.target_for(42, 0, rows, structures)
    source, _, _ = worker.sequence.decode_sequence(target.encode())
    assert source == rows[42]["response"]
    assert worker.prefix_for(42, 0, rows, structures) == ""


def test_prompt_forbids_repair_and_reference_feedback():
    prompt = worker.stream_prompt("Prove Demo", "Demo", 0)
    assert "CANONICAL TLA BYTE-SEQUENCE CONTRACT" in prompt
    assert "do not explain, repair" in prompt
    assert "insert targets" in prompt


def test_protected_eval_contract_does_not_load_response_text():
    text = open("tools/proof_fullmodule_canonical_sequence_sft_train.py").read()
    assert "protected_target_loaded=False" in text
    assert "protected_reference_conditioning=False" in text
    assert "Independent scoring owns the reference" in text
