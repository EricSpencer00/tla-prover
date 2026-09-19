#!/usr/bin/env python3
"""Build the metadata-only protected repair-and-extend pilot packet.

The packet binds a frozen evaluation denominator and its dependency closure, but
never copies TLA+ source, answers, model outputs, or repairs into the packet.
It is intentionally a local preflight step: submission and GPU execution are
separate actions that require all arm artifacts to be bound first.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))

from harness import gen_eval  # noqa: E402
from harness.runner import (  # noqa: E402
    build_module_index,
    local_deps,
    module_name,
)

HOLDOUT_SHA256 = "ecfc20533b9dc9a6e727ab989732310659d469eefbcc3705df72e3094ef54f78"
FORBIDDEN_FIELDS = {
    "answer",
    "candidate",
    "generated_text",
    "model_output",
    "output_text",
    "proof",
    "raw_reply",
    "reference_fragment",
    "repair",
    "response",
    "target",
}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def sha256_json(value: Any) -> str:
    return sha256_bytes(canonical_json(value))


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def _logical_external_path(path: Path, corpus: Path) -> str:
    try:
        return path.relative_to(corpus).as_posix()
    except ValueError:
        return path.as_posix()


def _logical_path(path: Path, corpus: Path) -> str:
    try:
        return path.relative_to(REPO).as_posix()
    except ValueError:
        return _logical_external_path(path, corpus)


def _family_tags() -> dict[str, str]:
    tags_path = REPO / "results" / "analysis" / "holdout_family_tags.jsonl"
    tags: dict[str, str] = {}
    for line in tags_path.read_text().splitlines():
        if not line.strip():
            continue
        row = json.loads(line)
        spec = str(row["spec"])
        if spec in tags:
            raise ValueError(f"duplicate family tag for spec {spec}")
        tags[spec] = row["family"]
    return tags


def _populations(holdout: dict[str, Any]) -> dict[str, str]:
    populations: dict[str, str] = {}
    for population, specs in holdout["by_population"].items():
        for spec in specs:
            key = str(spec)
            if key in populations:
                raise ValueError(f"spec {key} appears in multiple populations")
            populations[key] = population
    return populations


def _source_path(spec: str) -> tuple[Path, str]:
    patch = REPO / "corpus" / "configs" / "patches" / f"{spec}.tla"
    if patch.exists():
        return patch, f"corpus/configs/patches/{spec}.tla"
    return Path("__EXTERNAL_CORPUS__") / "tla_files" / f"{spec}.tla", f"tla_files/{spec}.tla"


def _resolve_source(spec: str, corpus: Path) -> tuple[Path, str, str]:
    path, logical = _source_path(spec)
    if path.name == f"{spec}.tla" and path.parent.name == "tla_files":
        path = corpus / logical
    if not path.exists():
        raise FileNotFoundError(f"missing canonical source for spec {spec}: {path}")
    text = path.read_text(errors="replace")
    mod = module_name(text)
    if not mod:
        raise ValueError(f"source for spec {spec} has no module declaration")
    return path, logical, mod


def _resolve_cfg_path(spec: str, corpus: Path) -> tuple[Path | None, str | None]:
    # Keep this order identical to harness.gen_eval's production order.
    options = [
        ("override", REPO / "corpus" / "configs" / "overrides" / f"{spec}.cfg"),
        ("original", corpus / "cfg" / f"{spec}.cfg"),
        ("draft", REPO / "corpus" / "configs" / "drafts" / f"{spec}.cfg"),
    ]
    for label, path in options:
        if path.exists():
            return path, label
    return None, None


def _dependency_closure(source_text: str, corpus: Path) -> list[dict[str, str]]:
    _, mod2path = build_module_index(corpus)
    pending = sorted(local_deps(source_text, mod2path))
    seen: set[str] = set()
    entries: list[dict[str, str]] = []
    while pending:
        mod = pending.pop(0)
        if mod in seen:
            continue
        seen.add(mod)
        path = mod2path[mod]
        text = path.read_text(errors="replace")
        entries.append(
            {
                "module": mod,
                "relpath": _logical_external_path(path, corpus),
                "sha256": sha256_file(path),
            }
        )
        pending.extend(sorted(local_deps(text, mod2path)))
    return sorted(entries, key=lambda entry: (entry["relpath"], entry["module"]))


def _policy_entry(spec: str) -> Any:
    policies = json.loads((REPO / "corpus" / "configs" / "policy.json").read_text())
    return policies.get(str(spec), {})


def _asset_hashes() -> dict[str, str]:
    candidates = [
        REPO / "harness" / "runner.py",
        REPO / "harness" / "gen_eval.py",
        REPO / "harness" / "proof_ladder_check.py",
        REPO / "tools" / "tla2tools.jar",
        REPO / "tools" / "tlapm" / "bin" / "tlapm",
    ]
    assets = {}
    for path in candidates:
        if path.exists() and path.is_file():
            assets[path.relative_to(REPO).as_posix()] = sha256_file(path)
    return assets


def _assert_no_answer_fields(value: Any, where: str = "packet") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in FORBIDDEN_FIELDS:
                raise AssertionError(f"answer-bearing field {where}.{key}")
            _assert_no_answer_fields(child, f"{where}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            _assert_no_answer_fields(child, f"{where}[{index}]")


def build_packet(corpus: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    holdout_path = REPO / "corpus" / "holdout_30.json"
    holdout = json.loads(holdout_path.read_text())
    holdout_sha = sha256_file(holdout_path)
    if holdout_sha != HOLDOUT_SHA256:
        raise AssertionError(f"frozen holdout hash changed: {holdout_sha}")
    specs = [str(spec) for spec in holdout["holdout_specs"]]
    if len(specs) != 30 or len(set(specs)) != 30:
        raise AssertionError("holdout must contain exactly 30 unique specs")

    closed = json.loads((REPO / "corpus" / "gate0_closed.json").read_text())
    closed_specs = {str(spec) for spec in closed["closed_local"]["specs"]}
    if not set(specs) <= closed_specs:
        raise AssertionError("holdout contains a spec outside frozen Gate-0 closure")

    tags = _family_tags()
    populations = _populations(holdout)
    if set(tags) != set(specs):
        raise AssertionError("family tags do not cover the exact frozen holdout")
    if set(populations) != set(specs):
        raise AssertionError("population tags do not cover the exact frozen holdout")

    cases = []
    for spec in sorted(specs, key=int):
        source, source_relpath, mod = _resolve_source(spec, corpus)
        cfg, cfg_label = _resolve_cfg_path(spec, corpus)
        population = populations[spec]
        cfg_applicable = population in {"state_machine", "expected_violation"}
        if cfg_applicable and cfg is None:
            raise AssertionError(f"applicable case {spec} has no cfg")
        policy = _policy_entry(spec)
        dependencies = _dependency_closure(source.read_text(errors="replace"), corpus)
        case = {
            "case_id": f"holdout-{int(spec):03d}",
            "spec": spec,
            "population": population,
            "family": tags[spec],
            "module_name": mod,
            "source": {
                "relpath": source_relpath,
                "sha256": sha256_file(source),
            },
            "cfg": {
                "applicable": cfg_applicable,
                "source_kind": cfg_label,
                "relpath": None if cfg is None else _logical_path(cfg, corpus),
                "sha256": None if cfg is None else sha256_file(cfg),
            },
            "policy_sha256": sha256_json(policy),
            "dependency_closure": dependencies,
        }
        cases.append(case)

    manifest = {
        "schema": 1,
        "kind": "protected_repair_extend_pilot_manifest_v1",
        "case_count": len(cases),
        "holdout_sha256": holdout_sha,
        "holdout_policy": "frozen_30_append_never",
        "case_order": [case["spec"] for case in cases],
        "cases": cases,
        "stratification": {
            "family_counts": dict(sorted(Counter(case["family"] for case in cases).items())),
            "population_counts": dict(sorted(Counter(case["population"] for case in cases).items())),
            "family_tag_source": "results/analysis/holdout_family_tags.jsonl",
            "population_source": "corpus/holdout_30.json",
        },
        "scoring": {
            "stages": ["sany", "tlc_nonvacuity", "tlaps_strict"],
            "independent_scorer_required": True,
            "worker_labels_are_not_scores": True,
            "not_applicable": {
                "library": ["tlc_nonvacuity", "tlaps_strict"],
                "proof_module": ["tlc_nonvacuity"],
                "state_machine": ["tlaps_strict"],
                "expected_violation": ["tlaps_strict"],
            },
        },
        "answer_bearing_content_included": False,
    }
    _assert_no_answer_fields(manifest, "manifest")

    packet = {
        "schema": 1,
        "kind": "protected_repair_extend_pilot_packet_v1",
        "manifest_sha256": sha256_json(manifest),
        "design": {
            "arms": ["base", "parent", "child", "child_repair"],
            "minimum_arms": 2,
            "four_arms_if_affordable": True,
            "arm_artifacts_must_be_bound_before_submission": True,
            "arm_artifact_hashes": {
                "base": None,
                "parent": None,
                "child": None,
                "child_repair": None,
            },
            "arm_artifact_binding_complete": False,
            "gpu_submission_blocked_until_arm_binding": True,
        },
        "candidate_budget": {
            "candidates_per_arm": 8,
            "repair_attempts": 2,
            "max_outputs_per_case_per_arm": 10,
            "repair_scope": "two highest-ranked candidates that fail the applicable verifier stage",
            "selection": "fixed per-arm seed schedule; verifier results cannot train or rank candidates",
        },
        "failure_mode_taxonomy": [
            "sany_contract",
            "tlc_nonvacuity",
            "tlaps_strict",
            "repair_budget_exhausted",
        ],
        "promotion_gate": {
            "certified_case": "independent strict pass of every applicable stage",
            "minimum_certified_cases": 3,
            "minimum_failure_modes": 2,
            "case_level_deduplication": True,
            "must_be_newly_certified_by_promoted_arm": True,
            "no_denominator_changes": True,
            "no_generated_feedback_or_reward": True,
        },
        "training_input_policy": {
            "holdout_answers_in_training": False,
            "holdout_reference_fragments_in_training": False,
            "holdout_repairs_in_training": False,
        },
        "claims": {
            "training_executed": False,
            "model_improvement_claim": False,
            "quality_claim": False,
            "proof_claim": False,
            "gate_claim": False,
            "generalization_claim": False,
            "tlc_claim": False,
            "nonvacuity_claim": False,
        },
        "scorer_assets": _asset_hashes(),
        "execution": {
            "gpu_submitted": False,
            "qsub_submitted": False,
            "local_preflight_only": True,
        },
    }
    _assert_no_answer_fields(packet, "packet")
    return manifest, packet


def build_stage(corpus: Path, output: Path) -> dict[str, Any]:
    if output.exists() and any(output.iterdir()):
        raise FileExistsError(f"refusing to overwrite non-empty stage: {output}")
    output.mkdir(parents=True, exist_ok=True)
    manifest, packet = build_packet(corpus)
    manifest_path = output / "manifest.json"
    packet_path = output / "packet.json"
    write_json(manifest_path, manifest)
    write_json(packet_path, packet)
    preflight = {
        "schema": 1,
        "kind": "protected_repair_extend_pilot_preflight_v1",
        "manifest_sha256": sha256_file(manifest_path),
        "packet_sha256": sha256_file(packet_path),
        "holdout_sha256": manifest["holdout_sha256"],
        "case_count": manifest["case_count"],
        "family_counts": manifest["stratification"]["family_counts"],
        "population_counts": manifest["stratification"]["population_counts"],
        "source_count": len(manifest["cases"]),
        "unique_source_hashes": len({case["source"]["sha256"] for case in manifest["cases"]}),
        "cfg_counts": {
            "applicable": sum(case["cfg"]["applicable"] for case in manifest["cases"]),
            "present": sum(case["cfg"]["sha256"] is not None for case in manifest["cases"]),
        },
        "dependency_count": sum(len(case["dependency_closure"]) for case in manifest["cases"]),
        "answer_bearing_content_found": False,
        "cuda_or_gpu_executed": False,
        "qsub_submitted": False,
        "independent_sany_tlc_tlaps_executed": False,
        "guards": [
            "frozen holdout hash",
            "Gate-0 closure membership",
            "exact family and population coverage",
            "canonical source/config/dependency hashes",
            "metadata-only answer leakage scan",
            "four-arm binding and GPU submission hold",
        ],
    }
    _assert_no_answer_fields(preflight, "preflight")
    preflight_path = output / "preflight.json"
    write_json(preflight_path, preflight)
    sums = "".join(
        f"{sha256_file(path)}  {path.name}\n"
        for path in (manifest_path, packet_path, preflight_path)
    )
    (output / "SHA256SUMS").write_text(sums)
    return preflight


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    preflight = build_stage(args.corpus.resolve(), (REPO / args.output).resolve() if not args.output.is_absolute() else args.output.resolve())
    print(json.dumps(preflight, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
