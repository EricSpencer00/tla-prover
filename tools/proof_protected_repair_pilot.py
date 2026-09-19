#!/usr/bin/env python3
"""Frozen protected repair-and-extend pilot for official TLAPS cases.

The packet builder is answer-free: it copies only the immutable theorem
scaffold and dependencies from the official typed packet.  The runner gives
each arm eight initial completions and, for feedback arms, at most two extra
repair calls.  Every candidate is extracted and checked by the independent
SANY-first strict TLAPS ladder before it can count as certified.

This pilot deliberately does not claim TLC coverage.  The official theorem
modules have no frozen TLC configuration, so TLC is recorded as not applicable
per case; the measurement canary remains the source of TLC/non-vacuity
calibration evidence.  A strict TLAPS pass still requires at least one
obligation and the audited proof-success classification.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

OFFICIAL_PACKET = ROOT / "results/runs/proof-typed-candidate-rank-official-20260917-v1/packet.json"
RANK_AUDIT = ROOT / "results/runs/proof-typed-candidate-rank-official-20260919-v1/independent-strict-score-v1/checks.jsonl"
SOURCE_MANIFEST = ROOT / "results/runs/proof-official-extension-manifest-20260905-v3/manifest.json"
LADDER_VERSION = "sany-strict-tlaps-ladder-v3"
MODEL_BASE = "openai/gpt-oss-120b"
MODEL_W4 = "chattla-w4dg-120b"
ARM_NAMES = ("base_one_shot", "base_feedback", "w4_one_shot", "w4_feedback")
TASKS_PER_PILOT = 20
INITIAL_ATTEMPTS = 8
MAX_REPAIRS = 2
MAX_TOKENS = 2048
VERIFIER_TIMEOUT = 30
SEED_BASE = 20260919


def sha(raw: bytes | str) -> str:
    if isinstance(raw, str):
        raw = raw.encode()
    return hashlib.sha256(raw).hexdigest()


def load_json(path: Path):
    return json.loads(path.read_text())


def audit_groups(path: Path) -> dict[str, dict]:
    """Summarize the previous answer-free audit without reading proof answers."""
    by_task: dict[str, list[dict]] = defaultdict(list)
    for line in path.read_text().splitlines():
        if line.strip():
            row = json.loads(line)
            by_task[row["task"]].append(row)
    out = {}
    for task, rows in by_task.items():
        first = rows[0]
        out[task] = {
            "prior_audit_status": first.get("status", "unmeasured"),
            "prior_audit_category": first.get("category", "unknown"),
            "prior_audit_rank1": first.get("rank") == 1,
            "prior_audit_attempts": len(rows),
        }
    return out


def stable_pick(rows: list[dict], n: int, salt: str) -> list[dict]:
    return sorted(rows, key=lambda r: sha(f"{salt}:{r['id']}"))[:n]


def build_packet(output: Path, official_packet: Path = OFFICIAL_PACKET,
                 rank_audit: Path = RANK_AUDIT,
                 source_manifest: Path = SOURCE_MANIFEST) -> dict:
    """Build the registered 20-case sample using only pre-run metadata."""
    source = load_json(official_packet)
    rows = source.get("rows")
    if not isinstance(rows, list) or len(rows) != 119:
        raise ValueError("official packet must contain exactly 119 rows")
    audit = audit_groups(rank_audit)
    manifest = load_json(source_manifest)
    categories = {row["id"]: row["category"] for row in manifest.get("tasks", [])}
    if len(categories) != 119:
        raise ValueError("source manifest must contain categories for all 119 tasks")
    enriched = []
    for row in rows:
        item = {
            "id": row["id"], "split": row["split"],
            "theorem_name": row["theorem_name"], "target_goal": row["target_goal"],
            # The historical official packet binds the proof fragment directly
            # to the theorem line.  The SANY-first ladder requires a proof
            # boundary on its own line, so freeze this one-byte renderer
            # normalization in the pilot packet rather than applying it during
            # scoring.
            "prefix": row["prefix"] if row["prefix"].endswith("\n") else row["prefix"] + "\n",
            "suffix": row["suffix"],
            "dependencies": row.get("dependencies", []),
        }
        item.update(audit.get(row["id"], {
            "prior_audit_status": "unmeasured",
            "prior_audit_category": categories[row["id"]],
            "prior_audit_rank1": False,
            "prior_audit_attempts": 0,
        }))
        enriched.append(item)

    # Allocate 10 distributed and 10 math cases.  Within each source family,
    # reserve equal slots for the observed prior failure families.  Unmeasured
    # tasks are a separate stratum so the pilot does not silently select only
    # tasks that were cheap for the prior ranker to verify.
    groups: dict[tuple[str, str], list[dict]] = defaultdict(list)
    for row in enriched:
        groups[(row["prior_audit_category"], row["prior_audit_status"])].append(row)
    quotas = {
        ("distributed_ind_inv", "pass"): 3,
        ("distributed_ind_inv", "timeout"): 5,
        ("math/minif2f", "pass"): 3,
        ("math/minif2f", "timeout"): 3,
        ("math/minif2f", "verifier_reject"): 4,
        ("math/proofnet", "unmeasured"): 2,
    }
    selected = []
    for key, quota in quotas.items():
        available = groups.get(key, [])
        if len(available) < quota:
            raise ValueError(f"stratum {key} has {len(available)} rows, need {quota}")
        selected.extend(stable_pick(available, quota, "protected-repair-pilot-v1"))
    selected.sort(key=lambda r: r["id"])
    if len(selected) != TASKS_PER_PILOT or len({r["id"] for r in selected}) != TASKS_PER_PILOT:
        raise ValueError("selection is not a unique 20-case sample")

    packet = {
        "schema": 1,
        "kind": "protected_repair_extend_pilot_packet",
        "registered_at_utc": "2026-09-19",
        "official_packet_sha256": sha(official_packet.read_bytes()),
        "rank_audit_sha256": sha(rank_audit.read_bytes()),
        "selection": {
            "method": "fixed 20-case stratified sample; stable SHA256(id) within prior audit status and source category",
            "salt": "protected-repair-pilot-v1",
            "quotas": {f"{a}|{b}": n for (a, b), n in quotas.items()},
            "answer_free": True,
            "reference_fragments_used": False,
            "candidate_proposals_used": False,
            "feedback_used": False,
            "prefix_boundary_normalization": "append one newline when the official theorem scaffold did not end one",
        },
        "budget": {
            "initial_attempts_per_case_arm": INITIAL_ATTEMPTS,
            "max_feedback_repairs": MAX_REPAIRS,
            "max_tokens": MAX_TOKENS,
            "verifier_timeout_seconds": VERIFIER_TIMEOUT,
            "arms": list(ARM_NAMES),
            "parameter_updates": 0,
        },
        "tlc": {
            "status": "not_applicable",
            "reason": "official theorem-proof packet has no frozen TLC configuration; TLC/non-vacuity measurement is covered by the canary",
        },
        "rows": selected,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    if output.exists():
        raise FileExistsError(output)
    output.write_text(json.dumps(packet, indent=2) + "\n")
    return packet


def prompt_for(task: dict, feedback: str | None = None) -> str:
    prompt = (
        "Complete the missing TLA+ proof fragment marked <PROOF_HOLE>. "
        "The theorem statement and all other module text are fixed. Return "
        "only the proof fragment, beginning with PROOF, BY, OBVIOUS, or a "
        "hierarchical <1> step, preferably in a tla code fence. Use valid "
        "TLAPS syntax. Do not repeat the module, theorem statement, or any "
        "candidate list. Do not introduce axioms, admissions, declarations, "
        "or comments.\n\n"
        f"Theorem: {task['theorem_name']}\nGoal: {task['target_goal']}\n\n"
        "===BEGIN FIXED MODULE SCAFFOLD===\n"
        + task["prefix"] + "<PROOF_HOLE>" + task["suffix"]
        + "\n===END FIXED MODULE SCAFFOLD==="
    )
    if feedback:
        prompt += (
            "\n\nThe previous attempt was not certified. Repair it using only "
            "the verifier evidence below. Return a replacement proof fragment "
            "only.\n===BEGIN VERIFIER FEEDBACK===\n" + feedback[-4000:] +
            "\n===END VERIFIER FEEDBACK==="
        )
    return prompt


def tail_feedback(result: dict) -> str:
    text = result.get("output") or result.get("reason") or ""
    if not text:
        text = f"status={result.get('status', 'unknown')}"
    return text[-4000:]


def extract(reply: str) -> str | None:
    from harness.proof_gen import extract_proof_block
    return extract_proof_block(reply)


def run(packet_path: Path, output: Path, base_model: str = MODEL_BASE,
        w4_model: str = MODEL_W4) -> dict:
    if output.exists():
        raise FileExistsError(output)
    packet = load_json(packet_path)
    if packet.get("kind") != "protected_repair_extend_pilot_packet":
        raise ValueError("wrong pilot packet kind")
    if len(packet.get("rows", [])) != TASKS_PER_PILOT:
        raise ValueError("pilot packet must contain 20 rows")
    output.mkdir(parents=True)
    (output / "packet.json").write_bytes(packet_path.read_bytes())
    config = {
        "schema": 1, "kind": "protected_repair_extend_pilot_run",
        "packet_sha256": sha(packet_path.read_bytes()),
        "models": {"base": base_model, "w4": w4_model},
        "arms": list(ARM_NAMES), "initial_attempts": INITIAL_ATTEMPTS,
        "max_feedback_repairs": MAX_REPAIRS, "max_tokens": MAX_TOKENS,
        "verifier_timeout_seconds": VERIFIER_TIMEOUT,
        "ladder_version": LADDER_VERSION, "parameter_updates": 0,
        "reference_fragments_used": False, "training_executed": False,
        "tlc_claim": False, "nonvacuity_claim": False, "gate_claim": False,
        "endpoint": os.environ.get("OPENAI_BASE_URL", ""),
        "extra_body": os.environ.get("OPENAI_EXTRA_BODY", "{}"),
    }
    (output / "config.json").write_text(json.dumps(config, indent=2) + "\n")
    from harness.proof_ladder_check import certify_fragment
    from harness.repair import make_model

    models = {
        "base_one_shot": make_model("openai:" + base_model),
        "base_feedback": make_model("openai:" + base_model),
        "w4_one_shot": make_model("openai:" + w4_model),
        "w4_feedback": make_model("openai:" + w4_model),
    }
    rows = []
    started = time.monotonic()
    with (output / "rows.jsonl").open("x") as ledger:
        for task_index, task in enumerate(packet["rows"]):
            for arm in ARM_NAMES:
                feedback = None
                model = models[arm]
                is_feedback = arm.endswith("feedback")
                max_calls = INITIAL_ATTEMPTS + (MAX_REPAIRS if is_feedback else 0)
                for attempt in range(max_calls):
                    prompt = prompt_for(task, feedback if is_feedback else None)
                    seed = SEED_BASE + task_index * 1000 + attempt
                    call_started = time.monotonic()
                    replies = model.generate_traced(
                        prompt, n=1,
                        temperature=0.0 if attempt == 0 else 0.7,
                        max_tokens=MAX_TOKENS, seed=seed)
                    reply, metadata = replies[0]
                    fragment = extract(reply)
                    row = {
                        "task": task["id"], "category": task.get("prior_audit_category"),
                        "arm": arm, "attempt": attempt, "seed": seed,
                        "prompt_sha256": sha(prompt), "raw_reply": reply,
                        "raw_reply_sha256": sha(reply), "fragment": fragment,
                        "model_metadata": metadata,
                        "generation_seconds": time.monotonic() - call_started,
                        "certified": False, "status": "no_proof_fragment",
                        "proved": 0, "total": 0,
                        "tlc_status": "not_applicable",
                    }
                    if fragment is not None:
                        result = certify_fragment(
                            task["prefix"], fragment, task["suffix"],
                            theorem_name=task["theorem_name"],
                            dependencies=tuple(Path(p) for p in task.get("dependencies", [])),
                            work_root=output / "checks" / arm / task["id"] / str(attempt),
                            timeout=VERIFIER_TIMEOUT,
                        )
                        row.update(result)
                        row["tlc_status"] = "not_applicable"
                    row["feedback_input_sha256"] = sha(feedback or "")
                    row["total_elapsed_seconds"] = time.monotonic() - started
                    ledger.write(json.dumps(row) + "\n")
                    ledger.flush()
                    rows.append(row)
                    print(json.dumps({k: row.get(k) for k in
                                      ("task", "arm", "attempt", "certified", "status")} ), flush=True)
                    if row.get("certified"):
                        break
                    if is_feedback:
                        feedback = tail_feedback(row)
                # one certified result is enough for this case/arm; remaining
                # candidate budget is not spent after a success.
    per_arm = {}
    for arm in ARM_NAMES:
        arm_rows = [r for r in rows if r["arm"] == arm]
        per_arm[arm] = {
            "attempts": len(arm_rows),
            "tasks": len({r["task"] for r in arm_rows}),
            "certified_tasks": len({r["task"] for r in arm_rows if r.get("certified")}),
            "sany_pass": sum(r.get("sany", {}).get("status") == "pass" for r in arm_rows),
            "statuses": dict(Counter(r.get("status", "unknown") for r in arm_rows)),
        }
    summary = {
        "schema": 1, "status": "completed", "tasks": TASKS_PER_PILOT,
        "rows": len(rows), "per_arm": per_arm,
        "certified_cases_any_arm": len({r["task"] for r in rows if r.get("certified")}),
        "certified_cases_spanning_arms": len({r["task"] for r in rows if r.get("certified")}),
        "elapsed_seconds": time.monotonic() - started,
        "promotion_gate": {
            "minimum_certified_cases": 3,
            "minimum_failure_families": 2,
            "passed": False,
            "note": "computed only after independent semantic/failure-family audit",
        },
        "training_executed": False, "tlc_claim": False,
        "nonvacuity_claim": False, "gate_claim": False,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    b = sub.add_parser("build-packet")
    b.add_argument("--output", type=Path, required=True)
    b.add_argument("--official-packet", type=Path, default=OFFICIAL_PACKET)
    b.add_argument("--rank-audit", type=Path, default=RANK_AUDIT)
    b.add_argument("--source-manifest", type=Path, default=SOURCE_MANIFEST)
    r = sub.add_parser("run")
    r.add_argument("--packet", type=Path, required=True)
    r.add_argument("--output", type=Path, required=True)
    r.add_argument("--base-model", default=MODEL_BASE)
    r.add_argument("--w4-model", default=MODEL_W4)
    a = p.parse_args()
    if a.command == "build-packet":
        packet = build_packet(a.output, a.official_packet, a.rank_audit, a.source_manifest)
        print(json.dumps({"output": str(a.output), "sha256": sha(a.output.read_bytes()),
                          "rows": len(packet["rows"])}))
    else:
        print(json.dumps(run(a.packet, a.output, a.base_model, a.w4_model), indent=2))


if __name__ == "__main__":
    main()
