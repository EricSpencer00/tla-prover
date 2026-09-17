import json
from pathlib import Path

import pytest

from tools import proof_fragment_delimited_pir as pir


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "results/runs/proof-multistep-manifest-20260905-v2/manifest.json"
CONTROLS = ROOT / "results/runs/proof-hierarchical-fresh-controls-20260905-v1/controls.json"
CONTROL_SUMMARY = ROOT / "results/runs/proof-hierarchical-fresh-controls-20260905-v1/summary.json"


def test_delimited_stream_is_lossless_for_all_training_fragments():
    _, train, _ = pir.load_manifest(MANIFEST)
    for task in train:
        stream = pir.encode_stream(task["reference_fragment"])
        assert pir.decode_stream(stream) == task["reference_fragment"]
        assert all(len(line.split("\t")) == 3 for line in stream.splitlines())


def test_delimited_decoder_rejects_framing_and_length_corruption():
    stream = pir.encode_stream("BY DEF TypeOK")
    assert pir.decode_stream(stream) == "BY DEF TypeOK"
    with pytest.raises(ValueError):
        pir.decode_stream(stream.replace("\t2\t", "\t3\t", 1))
    with pytest.raises(ValueError):
        pir.decode_stream(stream + "\ncomment")


def test_packet_builds_without_model_or_development_targets(tmp_path):
    summary = pir.build(MANIFEST, CONTROLS, CONTROL_SUMMARY, tmp_path / "packet")
    packet = json.loads((tmp_path / "packet" / "packet.json").read_text())
    assert summary["train_rows"] == 17
    assert summary["development_rows"] == 4
    assert packet["development_targets_exported"] is False
    assert all("target_stream" not in row for row in packet["development_rows"])
    assert packet["optimizer_updates"] == 0
