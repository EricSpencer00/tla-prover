import hashlib
import json

from tools.proof_official_wide_symbolic import load_manifest


def test_prepared_manifest_validates_from_reconstructed_bytes(tmp_path):
    tasks = []
    for index in range(119):
        prefix = f"---- MODULE M{index} ----\nTHEOREM T == TRUE\n"
        suffix = "\n====\n"
        tasks.append({
            "id": str(index), "split": "official_test", "category": "math",
            "prefix": prefix, "suffix": suffix, "source_sha256": hashlib.sha256(
                (prefix + suffix).encode()).hexdigest(),
            "theorem_name": "T", "symbolic_candidates": ["OBVIOUS"],
        })
    path = tmp_path / "manifest.json"
    path.write_text(json.dumps({"tasks": tasks,
                                "reference_fragments_used": False,
                                "training": False,
                                "legacy_retrieval_index_used": False}))
    _, loaded = load_manifest(path)
    assert len(loaded) == 119
