import json
from pathlib import Path

import pytest

from tools import proof_strategy_policy as policy


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "results/runs/proof-multistep-manifest-20260905-v2/manifest.json"


def test_strategy_classifier_is_train_shape_only():
    assert policy.strategy_for_fragment("BY DEF Init, TypeOK") == "direct_def"
    assert policy.strategy_for_fragment("<1>1. P\n  OBVIOUS") == "hierarchical"
    assert policy.strategy_for_fragment("BY SMT") == "other"


def test_build_is_answer_free_and_exact_population(tmp_path):
    result = policy.build(MANIFEST, tmp_path / "packet")
    packet_path = tmp_path / "packet" / "packet.json"
    packet = json.loads(packet_path.read_text())
    assert result["train_rows"] == 17
    assert result["development_rows"] == 4
    assert packet["development_targets_exported"] is False
    assert packet["reference_fragments_exported"] is False
    assert all("strategy_label" not in row for row in packet["development_rows"])
    assert all("reference_fragment" not in json.dumps(row) for row in packet["development_rows"])


def test_packet_round_trip(tmp_path):
    policy.build(MANIFEST, tmp_path / "packet")
    packet_path = tmp_path / "packet" / "packet.json"
    packet = policy.load_packet(packet_path, policy.sha(packet_path.read_bytes()))
    assert len(packet["train_rows"]) == 17
    assert len(packet["development_rows"]) == 4


def test_renderer_selects_only_matching_strategy(tmp_path):
    policy.build(MANIFEST, tmp_path / "packet")
    packet = json.loads((tmp_path / "packet" / "packet.json").read_text())
    for row in packet["development_rows"]:
        for strategy_id in range(len(policy.STRATEGIES)):
            chosen = policy.select_candidate(row, strategy_id)
            if chosen["candidate"] is not None:
                assert chosen["strategy"] == row["candidate_strategies"][chosen["candidate_index"]]


def test_manifest_hash_is_frozen(tmp_path):
    altered = tmp_path / "manifest.json"
    altered.write_bytes(MANIFEST.read_bytes() + b"\n")
    with pytest.raises(ValueError, match="manifest hash mismatch"):
        policy.build(altered, tmp_path / "packet")
