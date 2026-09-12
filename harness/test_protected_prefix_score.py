from copy import deepcopy
import json
from pathlib import Path
import sys

import pytest

from tools import protected_checkpoint_preflight as preflight
from tools import protected_prefix_score as scoring


def _packet_and_prefixes():
    rows, encodings, prefixes = [], [], {}
    for index in range(108):
        prompt = f"prompt-{index}"
        ident = preflight.WANTED_IDS.get(index, f"other-{index}")
        prefix = f"---- MODULE Row{index} ----\nPrefix{index} == TRUE\n"
        suffix = "Next == TRUE\n===="
        rows.append(dict(id=ident, prompt=prompt, response=prefix + suffix,
                         response_sha256=scoring.sha(prefix + suffix)))
        prompt_tokens = scoring.PROMPT_TOKENS.get(index, 1)
        encodings.append(dict(input_ids=[index] * prompt_tokens, prompt_tokens=prompt_tokens))
        prefixes[index] = (prefix, suffix)
    return dict(rows=rows, encodings=encodings), prefixes


def _identity(phase, model_files, parent_sha, child_sha):
    return dict(phase=phase, model_files=model_files, dtype_profile=preflight.PROFILE,
        checkpoint_sha256={"base": None, "parent": parent_sha, "child": child_sha}[phase],
        checkpoint_config=None if phase == "base" else {"kind": phase},
        final_layer_tensor_count=9, restored_parameter_count=0 if phase == "base" else 9,
        restored_tensors_exact=phase != "base", actual_tensors_exact=True,
        final_layer_sha256={f"tensor-{number}": str(number) * 64 for number in range(1, 10)})


@pytest.fixture
def valid(monkeypatch):
    packet, prefixes = _packet_and_prefixes()
    monkeypatch.setattr(scoring, "PREFIX", {
        row: (scoring.sha(prefixes[row][0]), supplied, reference)
        for row, (_, supplied, reference) in scoring.PREFIX.items()
    })
    model_files = {"config.json": "a" * 64}
    parent_sha, child_sha = scoring.PARENT_SHA, scoring.CHILD_SHA
    phase_weights = {phase: _identity(phase, model_files, parent_sha, child_sha)
                     for phase in scoring.PHASES}
    records = []
    for phase, row in scoring.PLAN:
        prefix, suffix = prefixes[row]
        continuation = suffix if phase == "base" else f"Next == {phase.upper()}_{row}\n===="
        ids = [row, len(phase), 1, 2]
        records.append(dict(phase=phase, row=row,
            generation_seed=scoring.SEED + row * 10,
            base_prompt_sha256=scoring.sha(f"prompt-{row}"),
            actual_user_prompt_tokens_match_frozen=True,
            actual_user_prompt_token_count=scoring.PROMPT_TOKENS[row],
            conditioned_input_token_ids=(
                [row] * scoring.PROMPT_TOKENS[row] + [0] * scoring.PREFIX[row][1]),
            supplied_prefix_sha256=scoring.PREFIX[row][0],
            supplied_prefix_tokens=scoring.PREFIX[row][1],
            reference_tokens=scoring.PREFIX[row][2],
            supplied_fraction=scoring.PREFIX[row][1] / scoring.PREFIX[row][2],
            reference_suffix_sha256=scoring.sha(suffix),
            reference_suffix_tokens=scoring.PREFIX[row][2] - scoring.PREFIX[row][1],
            continuation=continuation, continuation_sha256=scoring.sha(continuation),
            continuation_token_ids=ids, continuation_token_count=len(ids),
            continuation_matches_reference_suffix=continuation == suffix,
            raw_reply=prefix + continuation,
            raw_reply_sha256=scoring.sha(prefix + continuation),
            eos_ended=False, grammar_completed=False, finish_reason="other_stop",
            resolved_decode=dict(effective_num_beams=1, effective_do_sample=False,
                                 effective_mode="greedy_search"),
            selector_evidence=dict(method="ranked_greedy_primed_canonical_prefix",
                full_mask_audits=4, candidates_checked=10,
                actual_generated_ids_match=True),
            weights_identity=phase_weights[phase], grammar_enforced=True,
            reference_conditioning=True, training=False, supplied_reference_credit=False))
    receipt = dict(kind="protected_prefix_continuation_v1", complete=True,
        contract=dict(phases=list(scoring.PHASES), rows=list(scoring.ROWS),
            ordered_plan=[dict(phase=phase, row=row) for phase, row in scoring.PLAN],
            max_new_tokens=256, audit_steps=4, seed=scoring.SEED,
            grammar_enforced=True, reference_conditioning=True, training=False,
            supplied_reference_credit=False), packet_sha256=preflight.PACKET_SHA,
        parent_checkpoint_sha256=parent_sha, child_checkpoint_sha256=child_sha,
        corpus_sha256=scoring.replay.CORPUS_SHA, grammar_sha256=scoring.replay.GRAMMAR_SHA,
        model_files=model_files, phase_weights=phase_weights, records=records,
        gate_claim=False, model_improvement_claim=False)
    return packet, receipt


def test_complete_receipt_validates_exact_order_and_denominator(valid):
    packet, receipt = valid
    selected = preflight.protected_rows(packet)
    assert list(scoring.validate_receipt(receipt, selected)) == list(scoring.PLAN)


@pytest.mark.parametrize("mutation", [
    lambda r: r.update(complete=False),
    lambda r: r["contract"].update(max_new_tokens=255),
    lambda r: r["contract"].update(grammar_enforced=False),
    lambda r: r["contract"].update(reference_conditioning=False),
    lambda r: r["contract"].update(training=True),
    lambda r: r["contract"].update(supplied_reference_credit=True),
    lambda r: r.update(packet_sha256="0" * 64),
    lambda r: r.update(gate_claim=True),
    lambda r: r.update(model_improvement_claim=True),
    lambda r: r["records"].pop(),
    lambda r: r["records"].reverse(),
    lambda r: r["records"].append(deepcopy(r["records"][0])),
])
def test_receipt_and_contract_tampering_fail_closed(valid, mutation):
    packet, receipt = valid
    mutation(receipt)
    with pytest.raises(ValueError):
        scoring.validate_receipt(receipt, preflight.protected_rows(packet))


@pytest.mark.parametrize("mutation", [
    lambda x: x.update(raw_reply_sha256="0" * 64),
    lambda x: x.update(base_prompt_sha256="0" * 64),
    lambda x: x.update(actual_user_prompt_tokens_match_frozen=False),
    lambda x: x.update(supplied_prefix_sha256="0" * 64),
    lambda x: x.update(supplied_prefix_tokens=181),
    lambda x: x.update(reference_tokens=225),
    lambda x: x.update(supplied_fraction=.5),
    lambda x: x.update(reference_suffix_sha256="0" * 64),
    lambda x: x.update(raw_reply="changed", raw_reply_sha256=scoring.sha("changed")),
    lambda x: x.update(continuation_matches_reference_suffix=False),
    lambda x: x.update(continuation_token_count=3),
    lambda x: x.update(continuation_token_ids=[True]),
    lambda x: x.update(eos_ended=None),
    lambda x: x["resolved_decode"].update(effective_mode="beam_search"),
    lambda x: x["selector_evidence"].update(full_mask_audits=3),
    lambda x: x["selector_evidence"].update(actual_generated_ids_match=False),
    lambda x: x.update(weights_identity={}),
    lambda x: x.update(grammar_enforced=False),
    lambda x: x.update(reference_conditioning=False),
    lambda x: x.update(training=True),
    lambda x: x.update(supplied_reference_credit=True),
])
def test_record_tampering_fails_closed(valid, mutation):
    packet, receipt = valid
    mutation(receipt["records"][0])
    with pytest.raises(ValueError):
        scoring.validate_receipt(receipt, preflight.protected_rows(packet))


@pytest.mark.parametrize("mutation", [
    lambda r: r["phase_weights"]["base"].update(phase="parent"),
    lambda r: r["phase_weights"]["base"].update(actual_tensors_exact=False),
    lambda r: r["phase_weights"]["parent"].update(restored_tensors_exact=False),
    lambda r: r["phase_weights"]["child"].update(restored_parameter_count=8),
    lambda r: r["phase_weights"]["base"]["final_layer_sha256"].pop("tensor-1"),
    lambda r: r["phase_weights"].update(extra={}),
])
def test_phase_weight_marker_tampering_fails_closed(valid, mutation):
    packet, receipt = valid
    mutation(receipt)
    with pytest.raises(ValueError):
        scoring.validate_receipt(receipt, preflight.protected_rows(packet))


def test_only_specified_record_fields_are_required(valid):
    packet, receipt = valid
    specified = {"phase", "row", "base_prompt_sha256", "raw_reply", "raw_reply_sha256",
        "actual_user_prompt_tokens_match_frozen", "supplied_prefix_sha256",
        "supplied_prefix_tokens", "reference_tokens", "supplied_fraction",
        "continuation_token_ids", "continuation_token_count", "eos_ended",
        "grammar_completed", "finish_reason", "selector_evidence", "resolved_decode",
        "weights_identity", "conditioned_input_token_ids", "actual_user_prompt_token_count",
        "generation_seed", "grammar_enforced", "reference_conditioning", "training",
        "supplied_reference_credit", "reference_suffix_tokens", "continuation",
        "continuation_sha256", "reference_suffix_sha256",
        "continuation_matches_reference_suffix"}
    receipt["records"] = [{key: value for key, value in record.items() if key in specified}
                          for record in receipt["records"]]
    assert list(scoring.validate_receipt(receipt, preflight.protected_rows(packet))) == list(scoring.PLAN)


def test_malformed_header_is_explicit_raw_contract_rejection(tmp_path, monkeypatch):
    def forbidden(*args):
        raise AssertionError("Do not extract, repair, or pretend SANY ran")
    monkeypatch.setattr(scoring, "score", forbidden)
    text = "```tla\n---- MODULE M ----\n====\n```"
    result = scoring.score_candidate({"raw_reply": text}, tmp_path / "out", "java", "jar")
    assert result["status"] == "model_contract_reject" and not result["sany_invoked"]
    assert (tmp_path / "out/raw.txt").read_bytes() == text.encode()


def test_canonical_candidate_delegates_verbatim_and_preserves_infra_status(tmp_path, monkeypatch):
    text = "---- MODULE M ----\n\\* lexical EOF diagnostic\n===="
    def oracle(actual, output, java, jar):
        assert actual == text
        return {"status": "unmeasured_infrastructure", "detail": "lexical EOF"}
    monkeypatch.setattr(scoring, "score", oracle)
    assert scoring.score_candidate({"raw_reply": text}, tmp_path / "out", "java", "jar") == {
        "status": "unmeasured_infrastructure", "detail": "lexical EOF"}


def test_cli_scores_all_six_with_four_controls_and_no_gate_credit(
        valid, tmp_path, monkeypatch, capsys):
    packet, receipt = valid
    packet_path, receipt_path = tmp_path / "packet.json", tmp_path / "receipt.json"
    packet_path.write_text(json.dumps(packet))
    receipt_path.write_text(json.dumps(receipt))
    output = tmp_path / "score"

    def fake_file_sha(path):
        path = Path(path)
        if path == packet_path:
            return preflight.PACKET_SHA
        if path.name == "tla2tools.jar":
            return scoring.JAR_SHA
        return "f" * 64

    calls = []
    def oracle(text, destination, java, jar):
        calls.append(text)
        destination.mkdir(parents=True, exist_ok=False)
        if "SyntaxNegativeControl" in text:
            status = "model_sany_reject"
        elif "PARENT_47" in text:
            status = "unmeasured_infrastructure"
        else:
            status = "pass"
        return dict(status=status, candidate_sha256=scoring.sha(text))

    monkeypatch.setattr(scoring.preflight, "file_sha", fake_file_sha)
    monkeypatch.setattr(scoring.shutil, "which", lambda name: "/fake/java")
    monkeypatch.setattr(scoring, "score", oracle)
    monkeypatch.setattr(sys, "argv", ["protected_prefix_score", "--receipt", str(receipt_path),
        "--packet", str(packet_path), "--output", str(output)])
    scoring.main()

    summary = json.loads((output / "summary.json").read_text())
    rows = json.loads((output / "rows.json").read_text())
    controls = json.loads((output / "controls.json").read_text())
    assert len(calls) == 10 and len(controls) == 4 and len(rows) == 6
    assert [(row["phase"], row["row"]) for row in rows] == list(scoring.PLAN)
    assert rows[2]["status"] == "unmeasured_infrastructure"
    assert summary["counts"]["parent"] == {"unmeasured_infrastructure": 1, "pass": 1}
    assert summary["denominator"] == 6 and summary["observed"] == 6
    assert summary["scope"] == "two TRAIN rows; 72-81% supplied canonical reference; diagnostic only"
    assert not summary["complete"] and not summary["sany_pass_gate_credit"]
    assert not summary["gate_claim"] and not summary["model_improvement_claim"]
    assert json.loads(capsys.readouterr().out) == summary


def test_cli_help_exposes_only_final_receipt_packet_and_output():
    script = Path(__file__).resolve().parents[1] / "tools/protected_prefix_score.py"
    source = script.read_text()
    assert 'parser.add_argument("--receipt"' in source
    assert 'parser.add_argument("--packet"' in source
    assert 'parser.add_argument("--output"' in source
    assert "--records" not in source
