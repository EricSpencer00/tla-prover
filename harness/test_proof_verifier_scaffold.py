import json

import pytest

from tools.proof_verifier_scaffold import (
    build_index,
    build_prompt,
    load_index,
    obligation_shape,
    prepare_packet,
    query,
    render_hits,
)


def _row(**overrides):
    row = {
        "source": "examples",
        "module": "OtherModule",
        "module_path": "/tmp/OtherModule.tla",
        "module_id": "examples-1",
        "theorem_kind": "LEMMA",
        "theorem_name": "OtherLemma",
        "obligation_id": "1",
        "obligation_text": r"ASSUME NEW x \in Nat PROVE x + 1 \in Nat",
        "backend": "smt",
        "status": "proved",
    }
    row.update(overrides)
    return row


def _write_rows(path, rows):
    path.mkdir(parents=True)
    with (path / "rows.jsonl").open("w") as stream:
        for row in rows:
            stream.write(json.dumps(row) + "\n")


def test_shape_abstracts_identifiers_and_literals_but_keeps_structure():
    shape = obligation_shape(r"ASSUME NEW x \in Nat PROVE x + 17 \in Nat")
    assert "x" not in shape["signature"]
    assert "17" not in shape["signature"]
    assert "<id>" in shape["signature"]
    assert "<num>" in shape["signature"]
    assert shape["features"]["membership"] == 2


def test_index_excludes_module_and_answer_fields(tmp_path):
    trace = tmp_path / "trace"
    _write_rows(trace, [_row(), _row(module="HeldOut")])
    out = tmp_path / "index.jsonl"
    entries = build_index([trace], out, excluded_modules=["OtherModule"])
    assert len(entries) == 1
    assert "module" not in entries[0]
    assert "obligation_text" not in entries[0]
    assert "by_facts" not in entries[0]
    assert load_index(out) == entries

    contaminated = tmp_path / "contaminated"
    _write_rows(contaminated, [_row(reference_fragment="BY DEF Init")])
    with pytest.raises(ValueError, match="answer-bearing"):
        build_index([contaminated], tmp_path / "bad.jsonl")


def test_query_and_render_are_structural_and_verifier_conditioned(tmp_path):
    trace = tmp_path / "trace"
    _write_rows(trace, [_row()])
    out = tmp_path / "index.jsonl"
    build_index([trace], out)
    hits = query(out, r"ASSUME NEW y \in Nat PROVE y + 2 \in Nat")
    assert hits and hits[0]["backend"] == "smt"
    rendered = render_hits(hits)
    assert "BY" not in rendered
    assert "OtherLemma" not in rendered
    assert "obligation_text" not in rendered


def test_prompt_has_no_reference_argument_or_answer_context():
    hits = [{
        "shape_signature": "ASSUME NEW <id> \\in Nat PROVE <id> + <num> \\in Nat",
        "features": obligation_shape(r"ASSUME NEW x \in Nat PROVE x + 1 \in Nat")["features"],
        "backend": "smt", "theorem_kind": "LEMMA", "source_kind": "examples",
        "support_count": 1, "score": 1.0,
    }]
    prompt = build_prompt(
        "---- MODULE M ----\nLEMMA T == x = x\n",
        "T", "x = x", hits, {"sany": "pass", "failed_obligations": 0, "last_backend": "smt"})
    assert "BY DEF Init" not in prompt
    assert "reference" not in prompt.lower()
    assert "proof bodies withheld" in prompt
    assert "verifier_backend=smt" in prompt


def test_prepare_packet_never_exports_reference_fragment(tmp_path):
    trace = tmp_path / "trace"
    _write_rows(trace, [_row()])
    index = tmp_path / "index.jsonl"
    build_index([trace], index)
    manifest = tmp_path / "manifest.json"
    manifest.write_text(json.dumps({"tasks": [{
        "id": "t1", "split": "train", "source_family": "family",
        "theorem_name": "T", "target_goal": "x = x",
        "prefix": "---- MODULE M ----\nLEMMA T == x = x\n",
        "reference_fragment": "BY DEF Init",
    }]}))
    packet = prepare_packet(manifest, index, tmp_path / "packet")
    assert packet["reference_fragment_used"] is False
    assert packet["reference_fragment_exported"] is False
    assert packet["rows"][0]["prompt"].find("BY DEF Init") == -1
    assert "reference_fragment" not in packet["rows"][0]
