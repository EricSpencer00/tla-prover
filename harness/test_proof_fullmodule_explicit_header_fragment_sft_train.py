from tools import proof_fullmodule_explicit_header_fragment_sft_train as worker


def test_body_segments_exclude_header_and_reassemble():
    source = "---- MODULE Demo ----\nEXTENDS Naturals\n====\n"
    parts = worker.stream_segments(source, {}, 2)
    assert all("MODULE Demo" not in part for part in parts)
    assert "".join(parts) == "EXTENDS Naturals\n====\n"


def test_prompt_names_runtime_header_and_forbids_metadata():
    worker._HEADERS["Demo"] = "---- MODULE Demo ----\n"
    prompt = worker.stream_prompt("write a module", "Demo", 0, "---- MODULE Demo ----\nEXTENDS Naturals\n")
    assert "RUNTIME-SUPPLIED EXACT HEADER:" in prompt
    assert "CURRENT EXACT BODY PREFIX:\nEXTENDS Naturals" in prompt
    assert "MODULE: or SEGMENT:" in prompt
