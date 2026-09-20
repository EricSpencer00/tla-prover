import json
from pathlib import Path

import pytest

from tools.proof_teacher_anchor_development_score import validate_packet


def packet():
    return json.loads(Path("results/runs/proof-candidate-rank-base-20260905-v1/frozen.json").read_text())


def test_target_free_development_denominator():
    rows = validate_packet(packet())
    assert {row["id"] for row in rows} == {
        "crdt-type-step", "crdt-safety-step", "crdt-sum-type-proof", "crdt-sum-zero-proof"
    }
    assert all(len(row["candidates"]) == 29 for row in rows)
    assert all(row["context"]["reference_fragment_used"] is False for row in rows)


def test_development_packet_rejects_reference_field():
    rows = packet()
    rows[0]["reference_fragment"] = "BY SMT"
    with pytest.raises(ValueError, match="target or verifier"):
        validate_packet(rows)
