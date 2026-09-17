import json
from pathlib import Path

import pytest

from tools import proof_fragment_pir as pir


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "results/runs/proof-multistep-manifest-20260905-v2/manifest.json"
CONTROLS = ROOT / "results/runs/proof-hierarchical-fresh-controls-20260905-v1/controls.json"
CONTROL_SUMMARY = ROOT / "results/runs/proof-hierarchical-fresh-controls-20260905-v1/summary.json"


def test_typed_stream_is_lossless_for_all_training_fragments():
    _, train, _ = pir.load_manifest(MANIFEST)
    assert len(train) == 17
    for task in train:
        tokens = pir.typed_tokens(task["reference_fragment"])
        assert pir.decode_tokens(tokens) == task["reference_fragment"]
        assert {token["kind"] for token in tokens} <= {
            "whitespace", "number", "keyword", "identifier", "symbol"
        }


def test_development_rows_carry_no_answer_target():
    _, _, dev = pir.load_manifest(MANIFEST)
    for task in dev:
        clean = {key: task[key] for key in ("id", "split", "source_family", "source_sha256",
                                             "prefix", "suffix", "theorem_name", "dependencies")}
        pir.reject_answer_fields(clean)
        assert "reference_fragment" not in clean
        assert "pir_target" not in clean


def test_existing_strict_controls_are_complete():
    identity = pir.check_controls(CONTROLS, CONTROL_SUMMARY)
    assert identity["positive_controls"] == 17
    assert identity["omitted_controls"] == 17


def test_packet_builds_without_model_or_cuda(tmp_path):
    summary = pir.build(MANIFEST, CONTROLS, CONTROL_SUMMARY, tmp_path / "packet")
    packet = json.loads((tmp_path / "packet" / "packet.json").read_text())
    assert summary["train_rows"] == 17
    assert summary["development_rows"] == 4
    assert packet["development_targets_exported"] is False
    assert packet["optimizer_updates"] == 0
    assert all("pir_target" not in row for row in packet["development_rows"])


def test_answer_fields_fail_closed():
    with pytest.raises(ValueError, match="answer-bearing"):
        pir.reject_answer_fields({"x": {"pir_target": []}})
