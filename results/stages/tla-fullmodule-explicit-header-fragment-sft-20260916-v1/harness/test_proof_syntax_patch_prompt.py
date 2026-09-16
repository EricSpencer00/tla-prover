import json
import subprocess
import sys

from pathlib import Path

import pytest

from tools import proof_syntax_patch_prompt as prompt


SOURCE = """---- MODULE Frozen ----
EXTENDS Naturals

Init == x = 0
Next == x' = x
====
"""


def test_build_prompt_keeps_frozen_contract_and_source_signature():
    text = prompt.build_prompt(SOURCE, "row-47")
    assert "proof_syntax_patch_prompt_v1" in text
    assert "Frozen" in text
    assert "row-47" not in text  # row identifier remains external metadata
    assert "---- MODULE Frozen ----" in text
    assert "====" in text


def test_parse_accepts_single_json_with_fences():
    reply = """```json
{"op": "replace", "anchor": "Init == x = 0", "replacement": "Init == x = 1"}
```"""
    cand = prompt.parse_patch_candidate(reply)
    assert cand["op"] == "replace"
    assert cand["anchor"] == "Init == x = 0"


def test_parse_rejects_invalid_shapes_and_module_intrusion():
    with pytest.raises(ValueError, match="one anchored replace"):
        prompt.parse_patch_candidate("{}")
    with pytest.raises(ValueError, match="must not include module header"):
        prompt.parse_patch_candidate(json.dumps(
            {"op": "replace", "anchor": "x' = x", "replacement": "---- MODULE Bad ----"}))


def test_parse_rejects_doubly_escaped_line_breaks():
    reply = json.dumps({
        "op": "replace",
        "anchor": "Init == x = 0",
        "replacement": r"Init == x = 1\n    /\\ x \in Nat",
    })
    with pytest.raises(ValueError, match="decoded line breaks"):
        prompt.parse_patch_candidate(reply)


def test_apply_candidate_uses_shared_assembler_rules():
    raw = json.dumps({
        "op": "replace",
        "anchor": "x' = x",
        "replacement": "x' = x + 1",
    })
    assembled, candidate = prompt.apply_candidate(SOURCE, raw)
    assert candidate["op"] == "replace"
    assert "x' = x + 1" in assembled
    assert assembled.count("====") == 1
    assert assembled.startswith("---- MODULE Frozen ----")


def test_preflight_sany_is_unsupported_without_checkpoint(tmp_path, monkeypatch):
    jar = Path("local.jar")
    monkeypatch.setattr(prompt.syntax_train, "sany", lambda *_:
                        {"status": "infrastructure_error", "passed": None})
    reply = json.dumps({
        "op": "replace",
        "anchor": "x' = x",
        "replacement": "x' = x + 1",
    })
    result = prompt.preflight_sany(SOURCE, reply, tmp_path, jar=jar)
    assert result["sany"]["status"] == "infrastructure_error"


def test_direct_cli_import_smoke():
    runner = Path(prompt.__file__)
    completed = subprocess.run(
        [sys.executable, str(runner), "--help"],
        cwd=runner.parents[1], text=True, capture_output=True,
    )
    assert completed.returncode == 0, completed.stderr
