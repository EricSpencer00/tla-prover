import copy
import json

import pytest

from tools import proof_verifier_scaffold_score as score
from tools.proof_verifier_scaffold_cuda_eval import BUDGET


def fixture(tmp_path):
    prefix = "---------------- MODULE Demo ----------------\nTHEOREM Goal == TRUE\n"
    suffix = "\n===============================\n"
    packet = {
        "schema_version": 1,
        "packet_kind": "answer_free_verifier_conditioned_retrieval",
        "manifest_sha256": "a" * 64,
        "index_sha256": "b" * 64,
        "index_config_sha256": "c" * 64,
        "split": "development",
        "rows": [],
        "denominator": 4,
        "reference_fragment_used": False,
        "reference_fragment_exported": False,
        "proof_bodies_exported": False,
        "successful_candidates_exported": False,
        "model_executed": False,
        "training_executed": False,
        "parameter_updates": 0,
        "proof_or_quality_claim": False,
        "scope": "test",
    }
    for key in ("a", "b", "c", "d"):
        prompt = f"prompt {key}"
        packet["rows"].append({
            "id": key, "split": "development", "theorem_name": "Goal",
            "source_family": "test", "goal_shape": {}, "retrieval_hits": [],
            "prompt": prompt, "prompt_sha256": score.sha(prompt.encode()),
        })
    manifest = {
        "tasks": [{"id": key, "split": "development", "prefix": prefix,
                    "suffix": suffix, "theorem_name": "Goal", "dependencies": [],
                    "source_path": str(tmp_path / f"{key}.tla"),
                    "source_sha256": "d" * 64, "dependency_sha256": {}}
                   for key in ("a", "b", "c", "d")]
    }
    packet_path = tmp_path / "packet.json"
    packet_path.write_text(json.dumps(packet, indent=2) + "\n")
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(json.dumps(manifest) + "\n")
    generations = tmp_path / "generations"
    generations.mkdir()
    config = {
        "packet_sha256": score.sha(packet_path.read_bytes()),
        "checkpoint_sha256": "e" * 64,
        "budget": BUDGET,
        "restore_exact": True, "parameter_updates": 0,
        "training_executed": False, "reference_fragment_used": False,
        "proof_or_quality_claim": False,
    }
    (generations / "config.json").write_text(json.dumps(config))
    rows = []
    for packet_row in packet["rows"]:
        rendered = "rendered " + packet_row["prompt"]
        input_ids = [1, 2]
        reply = "BY SMT"
        tokens = [3, 4]
        rows.append({
            "id": packet_row["id"], "prompt_sha256": packet_row["prompt_sha256"],
            "rendered_prompt": rendered,
            "rendered_prompt_sha256": score.sha(rendered.encode()),
            "input_token_ids": input_ids,
            "input_token_ids_sha256": score.digest(input_ids), "input_tokens": 2,
            "status": "generated", "token_ids": tokens,
            "token_ids_sha256": score.digest(tokens), "output_tokens": 2,
            "hit_token_limit": False, "raw_reply": reply,
            "raw_reply_sha256": score.sha(reply.encode()),
        })
    (generations / "generations.jsonl").write_text(
        "".join(json.dumps(row) + "\n" for row in rows))
    return packet_path, manifest_path, generations, packet, manifest


def test_packet_rejects_answer_bearing_row(tmp_path):
    packet_path, _, _, packet, _ = fixture(tmp_path)
    packet["rows"][0]["reference_fragment"] = "BY SMT"
    with pytest.raises(ValueError):
        score.validate_packet(packet)


def test_generation_hash_tampering_rejected(tmp_path):
    packet_path, _, generations, packet, _ = fixture(tmp_path)
    raw = (generations / "generations.jsonl").read_text()
    row = json.loads(raw.splitlines()[0])
    row["raw_reply"] = "changed"
    (generations / "generations.jsonl").write_text(
        json.dumps(row) + "\n" + "\n".join(raw.splitlines()[1:]) + "\n")
    with pytest.raises(ValueError, match="output accounting"):
        score.validate_generations(packet, generations)


def test_generation_order_cannot_drop_interior_task(tmp_path):
    _, _, generations, packet, _ = fixture(tmp_path)
    rows = [json.loads(line) for line in (generations / "generations.jsonl").read_text().splitlines()]
    rows[1]["id"] = "d"
    (generations / "generations.jsonl").write_text(
        "".join(json.dumps(row) + "\n" for row in rows))
    with pytest.raises(ValueError, match="skips or reorders"):
        score.validate_generations(packet, generations)


def test_score_does_not_read_reference_fragment(tmp_path, monkeypatch):
    packet_path, manifest_path, generations, packet, manifest = fixture(tmp_path)
    for task in manifest["tasks"]:
        path = tmp_path / f"{task['id']}.tla"
        path.write_bytes(b"source")
        task["source_sha256"] = score.sha(path.read_bytes())
    manifest_path.write_text(json.dumps(manifest) + "\n")
    packet["manifest_sha256"] = score.sha(manifest_path.read_bytes())
    packet_path.write_text(json.dumps(packet, indent=2) + "\n")
    config = json.loads((generations / "config.json").read_text())
    config["packet_sha256"] = score.sha(packet_path.read_bytes())
    (generations / "config.json").write_text(json.dumps(config))
    # A checker that would fail if the source scorer passed an answer field.
    calls = []
    def checker(prefix, fragment, suffix, **kwargs):
        calls.append((prefix, fragment, suffix))
        return {"certified": True, "status": "pass", "proved": 1, "total": 1}
    summary = score.score(
        packet_path, manifest_path, generations, tmp_path / "scored",
        expected_packet_sha256=score.sha(packet_path.read_bytes()),
        expected_manifest_sha256=packet["manifest_sha256"],
        expected_checkpoint_sha256="e" * 64, checker=checker)
    assert summary["certified_tasks"] == 4
    assert len(calls) == 4
    assert summary["reference_fragment_read"] is False


def test_partial_generation_is_unmeasured_not_zero_success(tmp_path):
    packet_path, manifest_path, generations, packet, manifest = fixture(tmp_path)
    for task in manifest["tasks"]:
        path = tmp_path / f"{task['id']}.tla"
        path.write_bytes(b"source")
        task["source_sha256"] = score.sha(path.read_bytes())
    manifest_path.write_text(json.dumps(manifest) + "\n")
    packet["manifest_sha256"] = score.sha(manifest_path.read_bytes())
    packet_path.write_text(json.dumps(packet, indent=2) + "\n")
    config = json.loads((generations / "config.json").read_text())
    config["packet_sha256"] = score.sha(packet_path.read_bytes())
    (generations / "config.json").write_text(json.dumps(config))
    rows = (generations / "generations.jsonl").read_text().splitlines()[:2]
    (generations / "generations.jsonl").write_text("\n".join(rows) + "\n")
    summary = score.score(
        packet_path, manifest_path, generations, tmp_path / "scored",
        expected_packet_sha256=score.sha(packet_path.read_bytes()),
        expected_manifest_sha256=packet["manifest_sha256"],
        expected_checkpoint_sha256="e" * 64,
        checker=lambda *args, **kwargs: {"certified": False, "status": "verifier_reject",
                                         "proved": 0, "total": 1})
    assert summary["requested_rows"] == 4
    assert summary["measured_rows"] == 2
    assert summary["unmeasured_tasks"] == 4
