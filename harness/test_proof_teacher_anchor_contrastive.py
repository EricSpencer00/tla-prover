import json
from pathlib import Path

import pytest

from tools.proof_teacher_anchor_contrastive import validate_packet


def packet():
    return json.loads(Path(
        "results/stages/tla-teacher-anchor-contrastive-20260917-v6/packet.json"
    ).read_text())


def test_exact_train_only_teacher_contract():
    rows = validate_packet(packet())
    assert len(rows) == 17
    assert all(len(row["candidates"]) == 8 for row in rows)
    assert all(row["teacher_candidate_index"] == 0 for row in rows)
    assert all(row["development_target_exported"] is False for row in rows)
    assert all("reference_fragment" not in row for row in rows)


def test_packet_rejects_development_or_answer_fields():
    rows = packet()
    rows[0]["reference_fragment"] = "BY SMT"
    with pytest.raises(ValueError, match="answer or verifier"):
        validate_packet(rows)


def test_packet_rejects_wrong_teacher_index():
    rows = packet()
    rows[0]["teacher_candidate_index"] = 1
    with pytest.raises(ValueError, match="teacher anchor"):
        validate_packet(rows)
