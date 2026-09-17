import json
from pathlib import Path

import pytest

from tools import proof_fragment_pir_cuda_train as worker
from tools import proof_fragment_pir as pir


ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "results/runs/proof-fragment-pir-20260917-v2/packet.json"
DELIMITED_PACKET = ROOT / "results/runs/proof-fragment-delimited-pir-20260917-v1/packet.json"
PARENT_SHA = worker.PARENT_SHA256


def test_packet_preflight_is_cpu_only_and_hash_bound(tmp_path):
    parent = tmp_path / "parent.pt"
    parent.write_bytes(b"parent")
    with pytest.raises(ValueError, match="exact approved parent"):
        worker.preflight(PACKET, parent, worker.PACKET_SHA256, PARENT_SHA)


def test_decode_requires_exact_json_typed_stream():
    good = json.dumps([{"kind": "keyword", "text": "BY"}])
    result = worker.decode_pir_reply(good)
    assert result["valid"] is True
    assert result["fragment"] == "BY"
    assert worker.decode_pir_reply("```json\n" + good + "\n```")["valid"] is False
    assert worker.decode_pir_reply("[]")["valid"] is False


def test_packet_has_four_target_free_development_rows():
    packet = worker.load_packet(PACKET)
    assert pir.load_packet(PACKET)["packet_kind"] == packet["packet_kind"]
    assert len(packet["train_rows"]) == 17
    assert len(packet["development_rows"]) == 4
    assert all("pir_target" not in row for row in packet["development_rows"])
    assert all("reference_fragment" not in row for row in packet["development_rows"])


def test_worker_accepts_compact_delimited_packet_contract():
    packet = worker.load_packet(DELIMITED_PACKET, worker.DELIMITED_PACKET_SHA256)
    assert pir.load_packet(DELIMITED_PACKET)["packet_kind"] == packet["packet_kind"]
    assert packet["packet_kind"] == "frozen17_delimited_proof_fragment_pir"
    assert all("target_stream" in row for row in packet["train_rows"])
    assert all("target_stream" not in row for row in packet["development_rows"])


def test_preflight_does_not_import_torch_or_touch_cuda():
    source = Path(worker.__file__).read_text()
    assert "torch.cuda.is_available()" in source
    preflight_source = source.split("def train(", 1)[0]
    assert "torch.cuda" not in preflight_source


def test_score_source_supports_remote_dependency_rebinding_without_packet_change():
    source = (ROOT / "tools/proof_fragment_pir_score.py").read_text()
    assert "dependency_root / path.name" in source


def test_generation_uses_bf16_autocast_for_mixed_parent_layer():
    source = (ROOT / "tools/proof_fragment_pir_cuda_train.py").read_text()
    assert 'torch.autocast(device_type=device, dtype=torch.bfloat16)' in source
