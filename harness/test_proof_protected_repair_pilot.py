import json
from pathlib import Path

from tools.proof_protected_repair_pilot import (
    ARM_NAMES,
    INITIAL_ATTEMPTS,
    MAX_REPAIRS,
    MAX_TOKENS,
    build_packet,
    prompt_for,
)
from harness.repair import OpenAICompatModel


ROOT = Path(__file__).resolve().parents[1]


def test_registered_packet_is_twenty_case_answer_free(tmp_path):
    path = tmp_path / "packet.json"
    packet = build_packet(path)
    assert len(packet["rows"]) == 20
    assert len({row["id"] for row in packet["rows"]}) == 20
    assert packet["selection"]["answer_free"] is True
    assert packet["selection"]["reference_fragments_used"] is False
    assert packet["selection"]["candidate_proposals_used"] is False
    assert all("candidate_proposals" not in row for row in packet["rows"])
    assert all("reference_fragment" not in row for row in packet["rows"])


def test_prompt_contains_only_fixed_scaffold_and_feedback_is_bounded():
    task = {
        "id": "toy",
        "theorem_name": "Inductiveness",
        "target_goal": "P => P'",
        "prefix": "---- MODULE Toy ----\nTHEOREM Inductiveness == P\n",
        "suffix": "\n====",
    }
    prompt = prompt_for(task)
    assert "<PROOF_HOLE>" in prompt
    assert "candidate list" in prompt
    assert "reference_fragment" not in prompt
    feedback = "x" * 9000
    repaired = prompt_for(task, feedback)
    assert repaired.endswith("x" * 4000 + "\n===END VERIFIER FEEDBACK===")


def test_budget_contract_is_fixed():
    assert ARM_NAMES == ("base_one_shot", "base_feedback", "w4_one_shot", "w4_feedback")
    assert INITIAL_ATTEMPTS == 8
    assert MAX_REPAIRS == 2
    assert MAX_TOKENS == 2048


def test_model_specific_endpoint_overrides_global_route(monkeypatch):
    monkeypatch.setenv("OPENAI_BASE_URL", "https://shared.example/v1")
    monkeypatch.setenv("OPENAI_API_KEY", "shared")
    monkeypatch.setenv(
        "OPENAI_BASE_URL_CHATTLA_W4DGM_120B", "http://127.0.0.1:8321/v1"
    )
    monkeypatch.setenv("OPENAI_API_KEY_CHATTLA_W4DGM_120B", "local")

    model = OpenAICompatModel("chattla-w4dgm-120b")

    assert model.url == "http://127.0.0.1:8321/v1/chat/completions"
    assert model.key == "local"


def test_polaris_launcher_restores_credential_free_route_contract():
    launcher = (ROOT / "tools/protected_repair_pilot_polaris.pbs").read_text()
    assert "#PBS -V" in launcher
    assert (
        'export OPENAI_BASE_URL="${OPENAI_BASE_URL:-'
        "https://inference-api.alcf.anl.gov/resource_server/sophia/vllm/v1}"
    ) in launcher
    assert (
        'export OPENAI_API_KEY_CMD="${OPENAI_API_KEY_CMD:-'
        "$HOME/.venvs/alcf-inference/get_token.sh}"
    ) in launcher
    assert 'OPENAI_BASE_URL_OPENAI_GPT_OSS_120B' in launcher
    assert 'OPENAI_API_KEY_CMD_OPENAI_GPT_OSS_120B' in launcher
    assert 'OPENAI_BASE_URL_CHATTLA_W4DGM_120B' in launcher
    assert "EXPECTED_PACKET_SHA=a7902debb566503af613da6c28b0415953147e3fd1e14102853825d5dd9e5416" in launcher
