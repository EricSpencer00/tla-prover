import json

import pytest

from tools.proof_free_generation_sft import (
    extract_proof_block, prepare_manifest, training_tasks,
)


def task(ident, split, with_reference=True):
    row = {
        "id": ident, "split": split, "source_family": ident,
        "source_sha256": ident * 64, "assembled_sha256": (ident + "x") * 64,
        "prefix": f"---- MODULE M ----\nTHEOREM T == TRUE \\* {ident}\n",
        "suffix": "\n====\n", "theorem_name": "T", "module_name": "M",
        "dependencies": [], "standard_dependencies": [],
    }
    if with_reference:
        row["reference_fragment"] = "BY SMT"
    return row


def test_prepare_strips_development_answers(tmp_path):
    source = {"tasks": [task(f"tr{i}", "train") for i in range(17)] +
              [task(f"dv{i}", "development") for i in range(4)]}
    for row in source["tasks"]:
        row["reference_fragment"] = "BY SMT"
    src = tmp_path / "source.json"
    dst = tmp_path / "clean.json"
    src.write_text(json.dumps(source))
    receipt = prepare_manifest(src, dst)
    clean = json.loads(dst.read_text())
    assert receipt["development_reference_bytes_forwarded"] is False
    assert len([r for r in clean["tasks"] if r["split"] == "train"]) == 17
    assert len([r for r in clean["tasks"] if r["split"] == "development"]) == 4
    assert all("reference_fragment" in r for r in clean["tasks"] if r["split"] == "train")
    assert all("reference_fragment" not in r for r in clean["tasks"] if r["split"] == "development")
    training_tasks(clean)


def test_prepare_requires_source_development_reference(tmp_path):
    source = {"tasks": [task(f"tr{i}", "train") for i in range(17)] +
              [task(f"dv{i}", "development", with_reference=False) for i in range(4)]}
    src = tmp_path / "source.json"
    src.write_text(json.dumps(source))
    with pytest.raises(ValueError, match="source development"):
        prepare_manifest(src, tmp_path / "clean.json")


def test_training_tasks_rejects_answer_in_development():
    rows = ([task(f"tr{i}", "train") for i in range(17)] +
            [task(f"dv{i}", "development", with_reference=False) for i in range(4)])
    rows[-1]["proof_body"] = "BY SMT"
    with pytest.raises(ValueError, match="answer-bearing"):
        training_tasks({"tasks": rows})


@pytest.mark.parametrize("reply,expected", [
    ("```tla\nBY SMT\n```", "BY SMT"),
    ("text\n<1>1. OBVIOUS\n", "<1>1. OBVIOUS"),
    ("ordinary prose", None),
])
def test_extract_proof_block(reply, expected):
    assert extract_proof_block(reply) == expected
