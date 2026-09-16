"""Score the fixed supplied-prefix continuation diagnostic with SANY.

Most candidate bytes are canonical reference bytes supplied before generation.
This scorer therefore records syntax outcomes but never grants gate or model-
improvement credit, including when every assembled module passes SANY.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import shutil
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import protected_checkpoint_preflight as preflight
from tools import protected_reference_eos_replay as replay
from tools.protected_checkpoint_paired_generation import sha
from tools.protected_paired_sany_score import JAR_SHA, dump, module_name, score

PHASES = ("base", "parent", "child")
ROWS = (47, 107)
PLAN = tuple((phase, row) for phase in PHASES for row in ROWS)
PREFIX = {
    47: ("85691e1dd47493d3be2afd894e781bdaf6b77d3a8d43e9cae4fa26b8c0edbd5d", 182, 226),
    107: ("2c70fbec2364b35a803dffb1b17b40b58abbc0c7ce34569cf015dbc6e9eb5326", 488, 673),
}
PROMPT_TOKENS = {47: 401, 107: 457}
MAX_NEW_TOKENS = 256
AUDIT_STEPS = 4
SEED = 20261011
EOS_TOKEN_ID = 128009
PARENT_SHA = "fba2768ed9a8f629f6496dc1ef72763b32fc339c74ba9075d1ffc53acd6c2d1d"
CHILD_SHA = "b0399b51aed001051fe200751b3087fc008482ca9dfeb64eb12884f71eee3bb6"


def _sha256(value):
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def canonical_references(corpus):
    references = {}
    for item in corpus.get("references", []):
        row = item.get("row") if isinstance(item, dict) else None
        if row not in ROWS:
            continue
        reference = item.get("text")
        if row in references or not isinstance(reference, str) or sha(reference) != item.get("sha256"):
            raise ValueError("Canonical corpus reference identity mismatch")
        references[row] = item
    if set(references) != set(ROWS):
        raise ValueError("Canonical corpus must contain both protected rows")
    return references


def _reference_parts(item):
    reference = item["text"]
    if sha(reference) != item["sha256"]:
        raise ValueError("Reference control digest mismatch")
    try:
        marker = reference.index("Next ==")
    except ValueError as error:
        raise ValueError("Reference control lacks the frozen continuation marker") from error
    return reference, reference[:marker], reference[marker:]


def _validate_weights(receipt):
    weights = receipt.get("phase_weights")
    if not isinstance(weights, dict) or tuple(weights) != PHASES:
        raise ValueError("Exactly the three ordered phase weight identities required")
    model_files = receipt.get("model_files")
    if not isinstance(model_files, dict) or not model_files:
        raise ValueError("Model file identity missing")
    checkpoints = {
        "base": None,
        "parent": receipt.get("parent_checkpoint_sha256"),
        "child": receipt.get("child_checkpoint_sha256"),
    }
    if (checkpoints["parent"] != PARENT_SHA or checkpoints["child"] != CHILD_SHA):
        raise ValueError("Checkpoint identity missing")
    for phase in PHASES:
        identity = weights[phase]
        hashes = identity.get("final_layer_sha256") if isinstance(identity, dict) else None
        expected = dict(
            phase=phase,
            model_files=model_files,
            dtype_profile=preflight.PROFILE,
            checkpoint_sha256=checkpoints[phase],
            final_layer_tensor_count=9,
            restored_parameter_count=0 if phase == "base" else 9,
            restored_tensors_exact=phase != "base",
            actual_tensors_exact=True,
        )
        if (not isinstance(identity, dict) or
                any(identity.get(key) != value for key, value in expected.items()) or
                not isinstance(hashes, dict) or len(hashes) != 9 or
                not all(isinstance(name, str) and name and _sha256(value)
                        for name, value in hashes.items()) or
                (phase == "base") != (identity.get("checkpoint_config") is None)):
            raise ValueError(f"{phase} phase weight identity differs")
    return weights


def validate_receipt(receipt, selected, references):
    """Validate the complete generation contract before invoking any checker."""
    contract = receipt.get("contract")
    expected_plan = [dict(phase=phase, row=row) for phase, row in PLAN]
    if (receipt.get("kind") != "protected_prefix_continuation_v1" or
            receipt.get("complete") is not True or not isinstance(contract, dict) or
            contract.get("phases") != list(PHASES) or contract.get("rows") != list(ROWS) or
            contract.get("ordered_plan") != expected_plan or
            contract.get("max_new_tokens") != MAX_NEW_TOKENS or
            contract.get("audit_steps") != AUDIT_STEPS or contract.get("seed") != SEED or
            contract.get("grammar_enforced") is not True or
            contract.get("reference_conditioning") is not True or
            contract.get("training") is not False or
            contract.get("supplied_reference_credit") is not False or
            receipt.get("packet_sha256") != preflight.PACKET_SHA or
            receipt.get("corpus_sha256") != replay.CORPUS_SHA or
            receipt.get("grammar_sha256") != replay.GRAMMAR_SHA or
            receipt.get("parent_checkpoint_sha256") != PARENT_SHA or
            receipt.get("child_checkpoint_sha256") != CHILD_SHA or
            receipt.get("gate_claim") is not False or
            receipt.get("model_improvement_claim") is not False):
        raise ValueError("Complete protected prefix-continuation contract required")

    weights = _validate_weights(receipt)
    records = receipt.get("records")
    if (not isinstance(records, list) or len(records) != len(PLAN) or
            [(record.get("phase"), record.get("row"))
             for record in records if isinstance(record, dict)] != list(PLAN)):
        raise ValueError("Exactly six ordered phase/row records required")

    by_key = {}
    for record, (phase, row) in zip(records, PLAN):
        item, encoding = selected[row]
        reference, prefix, suffix = _reference_parts(references[row])
        prefix_sha, prefix_tokens, reference_tokens = PREFIX[row]
        continuation_ids = record.get("continuation_token_ids")
        conditioned_ids = record.get("conditioned_input_token_ids")
        resolved = record.get("resolved_decode")
        selector = record.get("selector_evidence")
        expected_prompt_tokens = encoding.get("prompt_tokens")
        if expected_prompt_tokens != PROMPT_TOKENS[row]:
            raise ValueError("Frozen packet prompt token count differs")
        if (record.get("phase") != phase or record.get("row") != row or
                sha(record.get("raw_reply", "")) != record.get("raw_reply_sha256") or
                sha(item["prompt"]) != record.get("base_prompt_sha256") or
                record.get("actual_user_prompt_tokens_match_frozen") is not True or
                record.get("actual_user_prompt_token_count") != expected_prompt_tokens or
                sha(prefix) != prefix_sha or record.get("supplied_prefix_sha256") != prefix_sha or
                record.get("supplied_prefix_tokens") != prefix_tokens or
                record.get("reference_tokens") != reference_tokens or
                record.get("supplied_fraction") != prefix_tokens / reference_tokens or
                record.get("reference_suffix_sha256") != sha(suffix) or
                not record.get("raw_reply", "").startswith(prefix) or
                type(record.get("continuation_matches_reference_suffix")) is not bool or
                record.get("continuation_matches_reference_suffix") is not
                (record.get("raw_reply") == reference)):
            raise ValueError("Raw output or supplied-reference identity differs")
        frozen_prompt_ids = encoding.get("input_ids", [])[:expected_prompt_tokens]
        if (not isinstance(conditioned_ids, list) or
                conditioned_ids[:expected_prompt_tokens] != frozen_prompt_ids or
                len(conditioned_ids) != expected_prompt_tokens + prefix_tokens):
            raise ValueError("Conditioned input does not preserve frozen prompt and prefix tokens")
        if (not isinstance(continuation_ids, list) or
                any(type(token) is not int or token < 0 for token in continuation_ids) or
                not 0 < len(continuation_ids) <= MAX_NEW_TOKENS or
                record.get("continuation_token_count") != len(continuation_ids) or
                type(record.get("eos_ended")) is not bool or
                type(record.get("grammar_completed")) is not bool):
            raise ValueError("Continuation token evidence differs")
        expected_finish = ("eos" if record["eos_ended"] else "token_limit"
                           if len(continuation_ids) == MAX_NEW_TOKENS else "other_stop")
        if (record["eos_ended"] != (continuation_ids[-1] == EOS_TOKEN_ID) or
                record.get("finish_reason") != expected_finish or
                (record["eos_ended"] and not record["grammar_completed"])):
            raise ValueError("Continuation termination evidence differs")
        if (not isinstance(resolved, dict) or resolved.get("effective_num_beams") != 1 or
                resolved.get("effective_do_sample") is not False or
                resolved.get("effective_mode") != "greedy_search" or
                not isinstance(selector, dict) or
                selector.get("method") != "ranked_greedy_primed_canonical_prefix" or
                selector.get("full_mask_audits") != AUDIT_STEPS or
                selector.get("actual_generated_ids_match") is not True or
                type(selector.get("candidates_checked")) is not int or
                selector.get("candidates_checked") < len(continuation_ids)):
            raise ValueError("Resolved greedy selector evidence differs")
        required_markers = {
            "generation_seed": SEED + row * 10,
            "grammar_enforced": True,
            "reference_conditioning": True,
            "training": False,
            "supplied_reference_credit": False,
            "reference_suffix_tokens": reference_tokens - prefix_tokens,
        }
        if (record.get("weights_identity") != weights[phase] or
                any(record.get(key) != value for key, value in required_markers.items())):
            raise ValueError("Per-record generation or phase identity differs")
        continuation = record.get("continuation")
        if (not isinstance(continuation, str) or
                record.get("continuation_sha256") != sha(continuation) or
                record["raw_reply"] != prefix + continuation):
            raise ValueError("Continuation text evidence differs")
        by_key[(phase, row)] = record
    return by_key


def score_candidate(record, output, java, jar):
    """Pass canonical raw bytes to the shared oracle without rewriting status."""
    text = record["raw_reply"]
    try:
        module_name(text)
    except ValueError:
        output.mkdir(parents=True, exist_ok=False)
        (output / "raw.txt").write_bytes(text.encode())
        result = dict(status="model_contract_reject", candidate_sha256=sha(text),
                      reason="Missing canonical module header; no extraction or repair",
                      sany_invoked=False)
        dump(output / "result.json", result)
        return result
    return score(text, output, java, jar)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if preflight.file_sha(args.packet) != preflight.PACKET_SHA:
        raise ValueError("Frozen packet mismatch")
    if preflight.file_sha(args.corpus) != replay.CORPUS_SHA:
        raise ValueError("Frozen canonical corpus mismatch")
    receipt = json.loads(args.receipt.read_bytes())
    selected = preflight.protected_rows(json.loads(args.packet.read_bytes()))
    references = canonical_references(json.loads(args.corpus.read_bytes()))
    by_key = validate_receipt(receipt, selected, references)

    jar = ROOT / "tools/tla2tools.jar"
    java = shutil.which("java")
    if java is None or preflight.file_sha(jar) != JAR_SHA:
        raise ValueError("Pinned SANY runtime unavailable")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    dump(output / "identity.json", dict(
        receipt_sha256=preflight.file_sha(args.receipt), packet_sha256=preflight.PACKET_SHA,
        corpus_sha256=replay.CORPUS_SHA,
        jar_sha256=JAR_SHA, scorer_sha256=preflight.file_sha(__file__),
        classifier_sha256=preflight.file_sha(ROOT / "harness/proof_ladder_check.py"),
        process_runner_sha256=preflight.file_sha(ROOT / "harness/proof_owned_process.py"),
        raw_reply_sha256={f"{phase}-{row}": by_key[(phase, row)]["raw_reply_sha256"]
                          for phase, row in PLAN}))

    controls = []
    for row in ROWS:
        reference, _, _ = _reference_parts(references[row])
        negative = re.sub(r"(?m)^={4,}\s*$", "SyntaxNegativeControl == )\n====", reference)
        if negative == reference:
            raise ValueError("Negative control injection failed")
        for label, text in (("reference", reference), ("negative", negative)):
            result = score(text, output / "controls" / f"{row}-{label}", java, jar)
            controls.append(dict(row=row, label=label, **result))
    dump(output / "controls.json", controls)
    controls_ok = all(result["status"] == ("pass" if result["label"] == "reference"
                                           else "model_sany_reject")
                      for result in controls)

    outcomes = []
    for phase, row in PLAN:
        result = score_candidate(by_key[(phase, row)],
                                 output / "candidates" / f"{row}-{phase}", java, jar)
        outcomes.append(dict(phase=phase, row=row, **result))
    dump(output / "rows.json", outcomes)
    terminal = {"pass", "model_sany_reject", "model_contract_reject"}
    summary = dict(
        complete=controls_ok and all(result["status"] in terminal for result in outcomes),
        controls_ok=controls_ok, requested=6, observed=6, denominator=6,
        generation_receipt_complete=True,
        counts={phase: dict(Counter(result["status"] for result in outcomes
                                    if result["phase"] == phase)) for phase in PHASES},
        supplied_fractions={str(row): PREFIX[row][1] / PREFIX[row][2] for row in ROWS},
        supplied_tokens={str(row): PREFIX[row][1] for row in ROWS},
        reference_tokens={str(row): PREFIX[row][2] for row in ROWS},
        continuation_matches_reference_suffix=sum(
            by_key[key]["continuation_matches_reference_suffix"] for key in PLAN),
        input_transform="none; raw_reply scored verbatim; no extraction, repair, or reclassification",
        scope="two TRAIN rows; 72-81% supplied canonical reference; diagnostic only",
        sany_pass_gate_credit=False, gate_claim=False, model_improvement_claim=False)
    dump(output / "summary.json", summary)
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
