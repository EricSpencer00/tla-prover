"""CPU-only admission contract for a sequence-level syntax-repair objective.

This module does not train or score a model.  It fails closed unless proposed
training data is separated from protected rows and the objective is materially
different from the retired token/span preference and full-response SFT paths.
"""
import hashlib
import json
from pathlib import Path

PROTECTED = (47, 107)
KIND = "sequence_pairwise_sany_repair_v1"
ALGORITHM = "full-response pairwise preference over verified-valid target and actual model rollout"
RETIRED = {
    "syntax_token_preference_v1",
    "syntax_structured_span_preference_v1",
    "response-only supervised mixed proof retention and full-module syntax",
}


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def validate(value):
    if value.get("kind") != KIND or value.get("algorithm") != ALGORITHM:
        raise ValueError("exact sequence-level objective required")
    if value.get("kind") in RETIRED or value.get("algorithm") in RETIRED:
        raise ValueError("retired objective reused")
    if value.get("protected_rows") != list(PROTECTED):
        raise ValueError("frozen protected denominator required")
    if value.get("protected_training") is not False or value.get("gate_claim") is not False:
        raise ValueError("protected data cannot train or grant gate credit")
    if value.get("retention") != {
        "rows": list(PROTECTED),
        "mode": "supplied_prefix_parent_replay",
        "required_sany_passes": 2,
        "credit": "zero",
    }:
        raise ValueError("exact zero-credit parent retention gate required")
    if value.get("evaluation") != {
        "rows": list(PROTECTED),
        "mode": "unchanged_unsupplied_frozen_prompts",
        "denominator": 2,
        "required_sany_passes": 2,
    }:
        raise ValueError("exact unsupplied evaluation gate required")
    pairs = value.get("pairs")
    if not isinstance(pairs, list) or not pairs:
        raise ValueError("nonempty sequence pairs required")
    seen = set()
    for pair in pairs:
        source_id = pair.get("source_id")
        if not isinstance(source_id, str) or not source_id or source_id in seen:
            raise ValueError("training source IDs must be nonempty and unique")
        if pair.get("protected_row") in PROTECTED:
            raise ValueError("protected rows cannot enter training pairs")
        seen.add(source_id)
        if pair.get("negative_origin") != "actual_model_rollout":
            raise ValueError("synthetic or reference-derived negatives are not admitted")
        if pair.get("positive_sany") is not True or pair.get("negative_sany") is not False:
            raise ValueError("positive-pass and rollout-reject SANY evidence required")
        positive, negative = pair.get("positive_tokens"), pair.get("negative_tokens")
        prompt = pair.get("prompt_tokens")
        if not isinstance(prompt, list) or not prompt or not all(type(t) is int and t >= 0 for t in prompt):
            raise ValueError("exact nonempty prompt-token prefix required")
        if not all(isinstance(x, list) and len(x) > 1 and all(type(t) is int and t >= 0 for t in x)
                   for x in (positive, negative)):
            raise ValueError("complete multi-token response sequences required")
        if positive == negative:
            raise ValueError("preference sequences must differ")
        eos = pair.get("eos_token_id")
        if type(eos) is not int or positive[-1] != eos:
            raise ValueError("preferred sequence must include EOS")
        if not isinstance(pair.get("rollout_receipt_sha256"), str) or len(pair["rollout_receipt_sha256"]) != 64:
            raise ValueError("actual rollout receipt identity required")
    expected = digest({"kind": KIND, "algorithm": ALGORITHM, "pairs": pairs})
    if value.get("objective_sha256") != expected:
        raise ValueError("objective identity mismatch")
    return value


def load(path):
    return validate(json.loads(Path(path).read_text()))
