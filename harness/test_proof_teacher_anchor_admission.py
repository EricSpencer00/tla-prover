import json
from pathlib import Path

from tools.proof_teacher_anchor_admission import build
from tools.proof_teacher_anchor_admission import target_scoped_pass


def test_target_scoped_parser_ignores_tlaps_library_prelude_only():
    result = {
        "returncode": 0, "timed_out": False,
        "candidate_path": "/tmp/AddTwo.tla",
        "output": '[INFO]: All 0 obligations proved.\n'
                  'File "./AddTwo.tla", line 1, character 1 to line 4, character 1:\n'
                  '[INFO]: All 8 obligations proved.\n',
    }
    assert target_scoped_pass(result) is True


def test_teacher_anchor_packet_is_train_only_and_bounded(tmp_path: Path):
    manifest = Path("results/runs/proof-multistep-manifest-20260905-v2/manifest.json")
    summary = build(manifest, tmp_path / "packet", negatives=2)
    assert summary["train_tasks"] == 17
    assert summary["teacher_anchor_count"] == 17
    assert summary["negative_candidate_count"] == 34
    assert summary["development_targets_exported"] is False
    packet = json.loads((tmp_path / "packet" / "packet.json").read_text())
    assert len(packet) == 17
    assert all(row["teacher_candidate_index"] == 0 for row in packet)
    assert all(row["development_target_exported"] is False for row in packet)
    assert all(row["context"]["teacher_anchor_train_only"] is True for row in packet)
    assert all("reference_fragment" not in row for row in packet)
