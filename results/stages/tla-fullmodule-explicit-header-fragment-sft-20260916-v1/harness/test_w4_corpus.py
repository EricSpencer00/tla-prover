"""Tests for the canonical W4 effective-corpus loader and grader.

These pin the three defects that made the SFT export disagree with the audit:
exclusions ignored, duplicates kept, and rows without an explicit "survived"
key silently dropped. Plus the non-W4 blast radius: de-duplicating w2-gen-*
would have cut the frozen 260-row v2_sft2 corpus to 196.
"""
from __future__ import annotations

import json

import pytest

from harness import corpus_prep, w4_corpus
from harness.corpus_prep import build_sft_file, load_survivors


def _write_shard(runs_dir, shard: int, rows: list[dict]) -> None:
    d = runs_dir / f"w4-opus-shard{shard}"
    d.mkdir(parents=True, exist_ok=True)
    with open(d / "w2_survivors.jsonl", "w") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")


def _row(key: str, **kw) -> dict:
    base = {
        "seed_key": f"w4opus::{key}",
        "cell": key,
        "spec_text": f"---- MODULE M{key} ----\nVARIABLES x\n====",
        "cfg_text": "INIT Init\nNEXT Next\nINVARIANT Inv",
        "nl": "A scenario.\nSAFETY PROPERTY: something holds.",
        "property_invariant": "Inv",
        "distinct_states": 100,
        "vacuity": [],
        "mutation_evidence": "no_kill",
        "features": {"noncomment_loc": 55, "num_variables": 5},
        "survived": True,
    }
    base.update(kw)
    return base


class TestLoadEffective:
    def test_drops_excluded_seed_keys(self, tmp_path):
        _write_shard(tmp_path, 0, [_row("d1-m1-p1-t1"), _row("d2-m2-p2-t2")])
        rows = w4_corpus.load_effective(
            exclusions={"excluded_seed_keys": ["w4opus::d1-m1-p1-t1"]}, runs_dir=tmp_path
        )
        assert [r["cell"] for r in rows] == ["d2-m2-p2-t2"]

    def test_first_wins_by_default(self, tmp_path):
        _write_shard(tmp_path, 0, [_row("d1-m1-p1-t1", distinct_states=1)])
        _write_shard(tmp_path, 1, [_row("d1-m1-p1-t1", distinct_states=999)])
        rows = w4_corpus.load_effective(exclusions={}, runs_dir=tmp_path)
        assert len(rows) == 1
        assert rows[0]["distinct_states"] == 1

    def test_keep_last_override_wins(self, tmp_path):
        _write_shard(tmp_path, 0, [_row("d1-m1-p1-t1", distinct_states=1)])
        _write_shard(tmp_path, 1, [_row("d1-m1-p1-t1", distinct_states=999)])
        rows = w4_corpus.load_effective(
            exclusions={"dedup_overrides": {"w4opus::d1-m1-p1-t1": "corrected"}},
            runs_dir=tmp_path,
        )
        assert len(rows) == 1
        assert rows[0]["distinct_states"] == 999

    def test_missing_survived_key_counts_as_survivor(self, tmp_path):
        r = _row("d1-m1-p1-t1")
        del r["survived"]
        _write_shard(tmp_path, 0, [r])
        assert len(w4_corpus.load_effective(exclusions={}, runs_dir=tmp_path)) == 1

    def test_explicit_survived_false_is_dropped(self, tmp_path):
        _write_shard(tmp_path, 0, [_row("d1-m1-p1-t1", survived=False)])
        assert w4_corpus.load_effective(exclusions={}, runs_dir=tmp_path) == []

    def test_numeric_not_lexical_shard_order(self, tmp_path):
        """Lexical order puts shard10 before shard2, so first-wins would pick
        the wrong duplicate. Shard 2 must win."""
        _write_shard(tmp_path, 2, [_row("d1-m1-p1-t1", distinct_states=2)])
        _write_shard(tmp_path, 10, [_row("d1-m1-p1-t1", distinct_states=10)])
        rows = w4_corpus.load_effective(exclusions={}, runs_dir=tmp_path)
        assert rows[0]["distinct_states"] == 2


class TestGrade:
    def test_safety_catch_is_diamond(self):
        assert w4_corpus.grade_row(_row("a", mutation_evidence="safety_catch")) == w4_corpus.DIAMOND

    def test_untrusted_mutation_evidence_demoted_to_bronze(self):
        r = _row("a", mutation_evidence="safety_catch")
        assert w4_corpus.grade_row(r, untrusted={r["seed_key"]}) == w4_corpus.BRONZE

    def test_structurally_strong_no_kill_is_gold(self):
        assert w4_corpus.grade_row(_row("a")) == w4_corpus.GOLD

    def test_below_loc_floor_is_silver(self):
        r = _row("a", features={"noncomment_loc": 12, "num_variables": 5})
        assert w4_corpus.grade_row(r) == w4_corpus.SILVER

    def test_vacuous_is_bronze(self):
        assert w4_corpus.grade_row(_row("a", vacuity=["only_1_state"])) == w4_corpus.BRONZE

    def test_missing_cfg_is_bronze(self):
        assert w4_corpus.grade_row(_row("a", cfg_text="")) == w4_corpus.BRONZE

    def test_arm_follows_liveness_property(self):
        assert w4_corpus.arm_of(_row("a")) == "safety"
        assert w4_corpus.arm_of(_row("a", liveness_property="Eventually")) == "liveness"

    def test_tier_and_arm_are_orthogonal(self):
        """A liveness row with no mutation catch is still gold, not promoted."""
        r = _row("a", liveness_property="Eventually", stutter_check="nontrivial")
        graded = w4_corpus.grade_corpus([r], exclusions={})[0]
        assert graded["tier_name"] == "gold"
        assert graded["arm"] == "liveness"


class TestLoadSurvivorsRouting:
    def test_w4_dirs_get_exclusions_applied(self, tmp_path, monkeypatch):
        _write_shard(tmp_path, 0, [_row("d1-m1-p1-t1"), _row("d1-m1-p1-t1")])
        monkeypatch.setattr(w4_corpus, "load_exclusions", lambda *a, **k: {})
        rows = load_survivors([tmp_path / "w4-opus-shard0"])
        assert len(rows) == 1, "duplicate seed_key must collapse for W4 dirs"

    def test_non_w4_dirs_are_not_deduped(self, tmp_path):
        """The frozen v2_sft2 corpus depends on this: w2-gen-* rows repeat
        seed_keys legitimately and must all survive."""
        d = tmp_path / "w2-gen-something"
        d.mkdir()
        with open(d / "w2_survivors.jsonl", "w") as f:
            for _ in range(3):
                f.write(json.dumps(_row("dup")) + "\n")
        assert len(load_survivors([d])) == 3

    def test_forcing_exclusions_on_non_w4_dirs_raises(self, tmp_path):
        d = tmp_path / "w2-gen-something"
        d.mkdir()
        (d / "w2_survivors.jsonl").write_text(json.dumps(_row("a")) + "\n")
        with pytest.raises(ValueError, match="not W4 shard dirs"):
            load_survivors([d], apply_exclusions=True)


class TestChatFormats:
    """Harmony is gpt-oss-specific. A Qwen tokenizer has no '<|channel|>' token,
    so rendering harmony for it would teach the model to emit literal control
    strings as text."""

    def test_harmony_still_default(self):
        out = corpus_prep.to_harmony_sft(_row("a"))
        assert "<|channel|>final<|message|>" in out["text"]
        assert out["text"].endswith("<|return|>")
        assert out["format"] == "harmony"

    def test_chatml_has_no_harmony_markup(self):
        out = corpus_prep.to_harmony_sft(_row("a"), fmt="chatml")
        t = out["text"]
        assert "<|im_start|>user\n" in t
        assert "<|im_start|>assistant\n" in t
        assert t.endswith("<|im_end|>")
        for tok in ("<|channel|>", "<|return|>", "<|start|>", "<|message|>"):
            assert tok not in t, f"harmony token {tok} leaked into chatml"
        assert out["format"] == "chatml"

    def test_both_formats_carry_the_same_payload(self):
        r = _row("a")
        h = corpus_prep.to_harmony_sft(r, fmt="harmony")["text"]
        c = corpus_prep.to_harmony_sft(r, fmt="chatml")["text"]
        for t in (h, c):
            assert "```tla" in t and "```cfg" in t
            assert r["spec_text"] in t and r["cfg_text"] in t and r["nl"] in t

    def test_unknown_format_rejected(self):
        with pytest.raises(ValueError, match="unknown format"):
            corpus_prep.to_harmony_sft(_row("a"), fmt="llama3")

    def test_build_sft_file_honors_format(self, tmp_path, monkeypatch):
        monkeypatch.setattr(w4_corpus, "load_exclusions", lambda *a, **k: {})
        _write_shard(tmp_path, 0, [_row("d1-m1-p1-t1")])
        out = tmp_path / "sft.jsonl"
        build_sft_file([tmp_path / "w4-opus-shard0"], out, fmt="chatml")
        rec = json.loads(out.read_text().strip())
        assert rec["format"] == "chatml"
        assert "<|channel|>" not in rec["text"]


class TestTieredSft:
    def test_min_tier_filters_and_tags(self, tmp_path, monkeypatch):
        monkeypatch.setattr(w4_corpus, "load_exclusions", lambda *a, **k: {})
        _write_shard(tmp_path, 0, [
            _row("d1-m1-p1-t1", mutation_evidence="safety_catch"),
            _row("d2-m2-p2-t2"),
            _row("d3-m3-p3-t3", features={"noncomment_loc": 9, "num_variables": 2}),
        ])
        out = tmp_path / "sft.jsonl"
        n = build_sft_file([tmp_path / "w4-opus-shard0"], out, min_tier=w4_corpus.DIAMOND)
        assert n == 1
        rec = json.loads(out.read_text().strip())
        assert rec["tier_name"] == "diamond"
        assert rec["arm"] == "safety"

    def test_min_tier_gold_keeps_diamond_and_gold(self, tmp_path, monkeypatch):
        monkeypatch.setattr(w4_corpus, "load_exclusions", lambda *a, **k: {})
        _write_shard(tmp_path, 0, [
            _row("d1-m1-p1-t1", mutation_evidence="safety_catch"),
            _row("d2-m2-p2-t2"),
            _row("d3-m3-p3-t3", features={"noncomment_loc": 9, "num_variables": 2}),
        ])
        out = tmp_path / "sft.jsonl"
        assert build_sft_file([tmp_path / "w4-opus-shard0"], out, min_tier=w4_corpus.GOLD) == 2
