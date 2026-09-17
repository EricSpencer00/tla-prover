from __future__ import annotations

import json
from pathlib import Path

from tools import proof_typed_agenda as agenda
from tools import proof_typed_agenda_score as scorer


ROOT = Path(__file__).resolve().parents[1]


def test_typed_agenda_receipts_bind_frozen_candidates_and_slots():
    packet_path = ROOT / "results/runs/proof-typed-agenda-20260917-v1/packet.json"
    job = ROOT / "results/runs/proof-typed-agenda-20260917-v1/job-7630589"
    packet = agenda.load_packet(packet_path, agenda.sha(packet_path.read_bytes()))
    expected = {row["id"]: row for row in packet["development_rows"]}
    for arm in ("base", "parent", "child"):
        rows = scorer.load_generations(job / f"{arm}_generations.json", packet)
        assert len(rows) == 4
        for row in rows:
            task = expected[row["id"]]
            assert row["candidate"] == task["candidate_proposals"][row["candidate_index"]]
            assert row["agenda_slots"] == task["candidate_agenda_slots"][row["candidate_index"]]


def test_typed_agenda_scorer_rejects_changed_agenda_slots(tmp_path):
    packet_path = ROOT / "results/runs/proof-typed-agenda-20260917-v1/packet.json"
    job = ROOT / "results/runs/proof-typed-agenda-20260917-v1/job-7630589"
    packet = agenda.load_packet(packet_path, agenda.sha(packet_path.read_bytes()))
    altered = json.loads((job / "child_generations.json").read_text())
    altered[0]["agenda_slots"] = ["close:qed"]
    path = tmp_path / "altered.json"
    path.write_text(json.dumps(altered))
    try:
        scorer.load_generations(path, packet)
    except ValueError as exc:
        assert "agenda slots" in str(exc)
    else:
        raise AssertionError("altered agenda slots were accepted")
