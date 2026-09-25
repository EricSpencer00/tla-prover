import json
import os
from pathlib import Path

import pytest

from tools.build_protected_repair_extend_pilot import (
    HOLDOUT_SHA256,
    _assert_no_answer_fields,
    build_packet,
)


CORPUS = Path(os.environ["TLA_BENCHMARK_DATA"]) if os.environ.get("TLA_BENCHMARK_DATA") else None


def _build_packet():
    if CORPUS is None or not CORPUS.is_dir():
        pytest.skip("set TLA_BENCHMARK_DATA to run against the private benchmark corpus")
    return build_packet(CORPUS)


def test_packet_is_frozen_metadata_only():
    manifest, packet = _build_packet()
    assert manifest["case_count"] == 30
    assert manifest["holdout_sha256"] == HOLDOUT_SHA256
    assert len(manifest["cases"]) == 30
    assert packet["candidate_budget"] == {
        "candidates_per_arm": 8,
        "max_outputs_per_case_per_arm": 10,
        "repair_attempts": 2,
        "repair_scope": "two highest-ranked candidates that fail the applicable verifier stage",
        "selection": "fixed per-arm seed schedule; verifier results cannot train or rank candidates",
    }
    assert packet["design"]["arms"] == ["base", "parent", "child", "child_repair"]
    assert packet["design"]["gpu_submission_blocked_until_arm_binding"] is True
    assert packet["claims"]["gate_claim"] is False
    _assert_no_answer_fields(manifest, "manifest")
    _assert_no_answer_fields(packet, "packet")


def test_stratification_and_dependency_hashes_are_complete():
    manifest, _ = _build_packet()
    assert manifest["stratification"]["family_counts"] == {
        "clocks_time": 2,
        "consensus": 1,
        "counters_registers": 3,
        "mutex_locks": 9,
        "network_channels": 2,
        "other": 12,
        "queues_buffers": 1,
    }
    assert manifest["stratification"]["population_counts"] == {
        "expected_violation": 1,
        "library": 4,
        "proof_module": 2,
        "state_machine": 23,
    }
    assert all(case["source"]["sha256"] for case in manifest["cases"])
    assert all(
        not case["cfg"]["relpath"].startswith("/")
        for case in manifest["cases"]
        if case["cfg"]["relpath"] is not None
    )
    assert all(
        dep["sha256"]
        for case in manifest["cases"]
        for dep in case["dependency_closure"]
    )
    assert sum(case["cfg"]["applicable"] for case in manifest["cases"]) == 24


def test_manifest_has_no_embedded_tla_or_output_text():
    manifest, packet = _build_packet()
    encoded = json.dumps({"manifest": manifest, "packet": packet})
    assert "---- MODULE" not in encoded
    assert "model_output" not in packet
    assert all("reference_fragment" not in case for case in manifest["cases"])
