import hashlib
import json

from tools.proof_official_candidate_tail import load_frozen


def test_tail_loader_binds_the_fixed_population(tmp_path):
    tasks = []
    for index in range(119):
        prefix = f"---- MODULE M{index} ----\nTHEOREM T == TRUE\n"
        suffix = "\n====\n"
        tasks.append({
            "id": str(index), "split": "official_test", "category": "math",
            "prefix": prefix, "suffix": suffix,
            "source_sha256": hashlib.sha256((prefix + suffix).encode()).hexdigest(),
            "theorem_name": "T", "symbolic_candidates": ["OBVIOUS"] * 1,
        })
    manifest = tmp_path / "manifest.json"
    manifest.write_text(json.dumps({"tasks": tasks,
                                    "reference_fragments_used": False,
                                    "training": False}))
    baseline_dir = tmp_path / "baseline"
    baseline_dir.mkdir()
    baseline = baseline_dir / "rows.jsonl"
    baseline.write_text("\n".join(json.dumps({"task": str(i), "certified": False})
                                  for i in range(119)) + "\n")
    (baseline_dir / "summary.json").write_text(json.dumps({"requested_tasks": 119}))
    _, loaded, passed = load_frozen(manifest, baseline)
    assert len(loaded) == 119
    assert not passed
