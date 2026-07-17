"""Tests for harness.lmgpa_bench (W3.1): manifest loading, decontam math,
and baseline resume logic. No real tlapm invocations except an optional
smoke path exercised manually via the CLI (--limit 1); here check_tlapm is
always stubbed.
"""
import json

from harness.lmgpa_bench import (load_manifest, decontam_report,
                                  run_baseline_tlapm, _read_done_ids)
from harness.corpora import NEAR_DUP_THRESHOLD


# --- manifest ----------------------------------------------------------------

def test_load_manifest_119_entries():
    manifest = load_manifest()
    assert len(manifest) == 119


def test_manifest_entries_have_required_fields():
    manifest = load_manifest()
    required = {"id", "category", "module_file", "theorem_name", "sha256"}
    for entry in manifest:
        assert required <= set(entry.keys())
        assert len(entry["sha256"]) == 64
        assert entry["theorem_name"]


def test_manifest_ids_unique():
    manifest = load_manifest()
    ids = [e["id"] for e in manifest]
    assert len(ids) == len(set(ids))


def test_manifest_categories_expected():
    manifest = load_manifest()
    cats = {e["category"] for e in manifest}
    assert "distributed_ind_inv" in cats
    assert any(c.startswith("math") for c in cats)


# --- decontam ------------------------------------------------------------------

DISTINCT_TEXT_A = """---- MODULE A ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
THEOREM Foo == Init /\\ Next => TRUE
====
"""

DISTINCT_TEXT_B = """---- MODULE B ----
VARIABLE y, z, w
Spec == y \\in Nat /\\ z \\in Nat /\\ w = y + z
Bar == \\A n \\in Nat : n >= 0
THEOREM Baz == Spec => Bar
====
"""


def _fake_manifest(tmp_path, text, id_="fake_theorem", category="synthetic"):
    lmgpa_root = tmp_path / "lmgpa"
    (lmgpa_root / "benchmarks" / category).mkdir(parents=True)
    mod_path = lmgpa_root / "benchmarks" / category / f"{id_}.tla"
    mod_path.write_text(text)
    manifest = [{
        "id": id_,
        "category": category,
        "module_file": f"benchmarks/{category}/{id_}.tla",
        "theorem_name": id_,
        "sha256": "0" * 64,
    }]
    return lmgpa_root, manifest


def test_decontam_near_duplicate_is_contaminated(tmp_path):
    lmgpa_root, manifest = _fake_manifest(tmp_path, DISTINCT_TEXT_A, id_="near_dup")
    # W2 "survivor" text is the same module with one token changed -- should
    # score very high Jaccard similarity, well above the threshold.
    near_dup_survivor = DISTINCT_TEXT_A.replace("x + 1", "x + 2")
    report = decontam_report(
        lmgpa_root=lmgpa_root, manifest=manifest,
        w2_texts={"survivor_1": near_dup_survivor},
        corpus206_texts={},
    )
    assert report["global_verdict"] == "contaminated"
    assert report["rows"][0]["verdict"] == "contaminated"
    assert report["rows"][0]["max_similarity"] >= NEAR_DUP_THRESHOLD


def test_decontam_distinct_text_is_clean(tmp_path):
    lmgpa_root, manifest = _fake_manifest(tmp_path, DISTINCT_TEXT_A, id_="distinct")
    report = decontam_report(
        lmgpa_root=lmgpa_root, manifest=manifest,
        w2_texts={"unrelated": DISTINCT_TEXT_B},
        corpus206_texts={"unrelated2": DISTINCT_TEXT_B},
    )
    assert report["global_verdict"] == "clean"
    assert report["rows"][0]["verdict"] == "clean"
    assert report["rows"][0]["max_similarity"] < NEAR_DUP_THRESHOLD


def test_decontam_empty_canonical_sets_is_clean(tmp_path):
    lmgpa_root, manifest = _fake_manifest(tmp_path, DISTINCT_TEXT_A, id_="alone")
    report = decontam_report(lmgpa_root=lmgpa_root, manifest=manifest,
                              w2_texts={}, corpus206_texts={})
    assert report["global_verdict"] == "clean"
    assert report["n_w2_survivor_texts"] == 0
    assert report["n_corpus206_texts"] == 0


def test_decontam_report_written_to_out_path(tmp_path):
    lmgpa_root, manifest = _fake_manifest(tmp_path, DISTINCT_TEXT_A, id_="writeout")
    out_path = tmp_path / "out" / "lmgpa_decontam.json"
    decontam_report(lmgpa_root=lmgpa_root, manifest=manifest,
                     w2_texts={}, corpus206_texts={}, out_path=out_path)
    assert out_path.exists()
    on_disk = json.loads(out_path.read_text())
    assert on_disk["n_theorems"] == 1


# --- baseline resume logic ------------------------------------------------------

def _stub_checker(status, proved, total, seconds=1.0):
    def checker(tla_file, workdir, timeout=600):
        return status, proved, total, "stub output", seconds
    return checker


def _small_manifest(n=3):
    return [{
        "id": f"t{i}",
        "category": "synthetic",
        "module_file": f"benchmarks/synthetic/t{i}.tla",
        "theorem_name": f"t{i}",
        "sha256": "0" * 64,
    } for i in range(n)]


def _write_fake_modules(lmgpa_root, manifest):
    for entry in manifest:
        mod_path = lmgpa_root / entry["module_file"]
        mod_path.parent.mkdir(parents=True, exist_ok=True)
        mod_path.write_text(f"---- MODULE {entry['id']} ----\n====\n")


def test_baseline_writes_one_row_per_module(tmp_path):
    lmgpa_root = tmp_path / "lmgpa"
    manifest = _small_manifest(3)
    _write_fake_modules(lmgpa_root, manifest)
    out_dir = tmp_path / "run"

    rows_path = run_baseline_tlapm(out_dir, lmgpa_root=lmgpa_root, manifest=manifest,
                                    checker=_stub_checker("pass", 2, 2))
    rows = [json.loads(l) for l in rows_path.read_text().splitlines()]
    assert len(rows) == 3
    assert {r["id"] for r in rows} == {"t0", "t1", "t2"}
    assert all(r["status"] == "pass" for r in rows)


def test_baseline_resumes_skipping_done_ids(tmp_path):
    lmgpa_root = tmp_path / "lmgpa"
    manifest = _small_manifest(3)
    _write_fake_modules(lmgpa_root, manifest)
    out_dir = tmp_path / "run"
    out_dir.mkdir(parents=True)
    (out_dir / "rows.jsonl").write_text(
        json.dumps({"id": "t0", "status": "pass", "proved": 1, "total": 1, "seconds": 0.5}) + "\n"
    )

    calls = []
    def checker(tla_file, workdir, timeout=600):
        calls.append(tla_file.stem)
        return "pass", 1, 1, "stub", 0.1

    rows_path = run_baseline_tlapm(out_dir, lmgpa_root=lmgpa_root, manifest=manifest,
                                    checker=checker)
    rows = [json.loads(l) for l in rows_path.read_text().splitlines()]
    assert len(rows) == 3
    # only t1/t2 were actually invoked; t0 was skipped as already-done
    assert set(calls) == {"t1", "t2"}


def test_baseline_respects_limit(tmp_path):
    lmgpa_root = tmp_path / "lmgpa"
    manifest = _small_manifest(3)
    _write_fake_modules(lmgpa_root, manifest)
    out_dir = tmp_path / "run"

    rows_path = run_baseline_tlapm(out_dir, lmgpa_root=lmgpa_root, manifest=manifest[:1],
                                    checker=_stub_checker("timeout", 0, 0))
    rows = [json.loads(l) for l in rows_path.read_text().splitlines()]
    assert len(rows) == 1
    assert rows[0]["status"] == "timeout"


def test_read_done_ids_ignores_malformed_lines(tmp_path):
    rows_path = tmp_path / "rows.jsonl"
    rows_path.write_text('{"id": "a"}\nnot json\n{"id": "b"}\n\n')
    assert _read_done_ids(rows_path) == {"a", "b"}


def test_read_done_ids_missing_file_is_empty(tmp_path):
    assert _read_done_ids(tmp_path / "does_not_exist.jsonl") == set()
