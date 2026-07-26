"""Tests for harness/corpus_prep.py (S2 collapse-check, S5 family tagging,
harmony SFT formatter). Fixtures only -- no dependency on live w2-gen runs or
the real holdout-30 (those are exercised via the CLI in production runs)."""
import json
from pathlib import Path

import pytest

from harness import corpus_prep as cp


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

TRIVIAL_SPEC = """---- MODULE Trivial ----
VARIABLES x
Init == x = 0
Next == x' = x
====
"""

RICH_SPEC = """---- MODULE Rich ----
EXTENDS Naturals, FiniteSets, Sequences
VARIABLES pc, x, y, b, S
Init ==
 /\\ pc = 0
 /\\ x = 0
 /\\ y = 0
 /\\ b = FALSE
 /\\ S = {}
Foo(i) ==
 /\\ pc = 0
 /\\ \\/ x' = x + 1
    \\/ y' = y + 1
 /\\ UNCHANGED <<pc, b, S>>
Bar(i) ==
 /\\ pc = 1
 /\\ b' = ~b
 /\\ UNCHANGED <<pc, x, y, S>>
Spec == Init /\\ [][Foo(1) \\/ Bar(1)]_<<x,y,b>> /\\ WF_x(Foo(1))
Safety == []( x >= 0 )
====
"""


def _mk_survivor_row(seed_key, nl, spec_text, cfg_text="CONSTANTS\nINIT Init\nNEXT Next\n"):
    from harness.adequacy import structural_features, complexity_score
    feats = structural_features(spec_text)
    return {
        "survived": True,
        "seed_key": seed_key,
        "nl": nl,
        "module": seed_key,
        "spec_text": spec_text,
        "cfg_text": cfg_text,
        "features": feats,
        "complexity_score": complexity_score(feats),
        "source": "fixture",
    }


@pytest.fixture
def survivor_dir(tmp_path):
    d = tmp_path / "run1"
    d.mkdir()
    rows = [
        _mk_survivor_row("seed_trivial_1", "A trivial mutex spec for two processes.", TRIVIAL_SPEC),
        _mk_survivor_row("seed_rich_1", "A Paxos-like consensus protocol with quorum voting and leader election.", RICH_SPEC),
    ]
    with open(d / "w2_survivors.jsonl", "w") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")
    return d


@pytest.fixture
def empty_survivor_dir(tmp_path):
    d = tmp_path / "empty_run"
    d.mkdir()
    return d


@pytest.fixture
def holdout_corpus(tmp_path):
    # A tiny fixture holdout corpus dir with canonical .tla files + a manifest
    # json mirroring corpus/holdout_30.json's holdout_specs shape.
    tla_dir = tmp_path / "canonical"
    tla_dir.mkdir()
    (tla_dir / "1.tla").write_text(RICH_SPEC)
    (tla_dir / "2.tla").write_text(RICH_SPEC)
    manifest = {"holdout_specs": [1, 2]}
    manifest_path = tmp_path / "holdout.json"
    manifest_path.write_text(json.dumps(manifest))
    return manifest_path, tla_dir


# ---------------------------------------------------------------------------
# S2 collapse-check
# ---------------------------------------------------------------------------

class TestCollapseReport:
    def test_collapse_flag_false_when_comparable(self, survivor_dir, holdout_corpus, monkeypatch):
        manifest_path, tla_dir = holdout_corpus
        monkeypatch.setattr(cp, "_canonical_spec_path", lambda n: tla_dir / f"{n}.tla")
        report = cp.collapse_report([survivor_dir], manifest_path)
        assert isinstance(report, dict)
        assert "collapse_flag" in report
        assert "features" in report
        assert report["survivor_count"] == 2
        assert report["holdout_count"] == 2

    def test_collapse_flag_true_when_survivors_are_trivial(self, tmp_path, holdout_corpus, monkeypatch):
        manifest_path, tla_dir = holdout_corpus
        monkeypatch.setattr(cp, "_canonical_spec_path", lambda n: tla_dir / f"{n}.tla")
        d = tmp_path / "trivial_run"
        d.mkdir()
        rows = [_mk_survivor_row(f"s{i}", "trivial", TRIVIAL_SPEC) for i in range(5)]
        with open(d / "w2_survivors.jsonl", "w") as f:
            for r in rows:
                f.write(json.dumps(r) + "\n")
        report = cp.collapse_report([d], manifest_path)
        assert report["collapse_flag"] is True

    def test_empty_survivor_dirs_robust(self, empty_survivor_dir, holdout_corpus, monkeypatch):
        manifest_path, tla_dir = holdout_corpus
        monkeypatch.setattr(cp, "_canonical_spec_path", lambda n: tla_dir / f"{n}.tla")
        report = cp.collapse_report([empty_survivor_dir], manifest_path)
        assert report["survivor_count"] == 0
        # No crash; collapse_flag should be a well-defined bool (False when no data).
        assert report["collapse_flag"] is False

    def test_collapse_ratio_constant_documented(self):
        assert cp.COLLAPSE_RATIO == 0.5


# ---------------------------------------------------------------------------
# S5 family tagging
# ---------------------------------------------------------------------------

class TestTagFamily:
    @pytest.mark.parametrize("text,expected", [
        ("A Paxos consensus protocol with quorum voting and leader election", "consensus"),
        ("raft leader election among ballot boxes", "consensus"),
        ("Two-phase commit for distributed transactions (2PC)", "commit_protocols"),
        ("Peterson's algorithm for mutual exclusion using a lock", "mutex_locks"),
        ("A bounded FIFO buffer with producer and consumer processes", "queues_buffers"),
        ("Cache coherence protocol for a shared memory model", "caches_memory"),
        ("Lamport timestamp and vector timestamp ordering algorithm", "clocks_time"),
        ("Log replication for a replicated key-value storage system", "replication_storage"),
        ("Gossip broadcast protocol over an asynchronous message channel", "network_channels"),
        ("A simple incrementing counter with a shared register", "counters_registers"),
        ("A completely unrelated spec about nothing in particular", "other"),
    ])
    def test_taxonomy_keywords(self, text, expected):
        assert cp.tag_family(text) == expected

    def test_case_insensitive(self):
        assert cp.tag_family("PAXOS QUORUM BALLOT") == "consensus"

    def test_first_match_wins_order(self):
        # "lock" (mutex_locks) appears after "queue" (queues_buffers) in the
        # taxonomy order defined in the spec; queues_buffers keyword should
        # not accidentally beat an earlier-order family. Use a string that
        # contains both a consensus keyword and a mutex keyword: consensus
        # is declared first, so it should win.
        text = "paxos-based mutex lock service"
        assert cp.tag_family(text) == "consensus"

    def test_deterministic_repeated_calls(self):
        text = "two-phase commit transaction"
        results = {cp.tag_family(text) for _ in range(5)}
        assert results == {"commit_protocols"}

    def test_tag_corpus_counts_and_overlap(self, survivor_dir, holdout_corpus, monkeypatch, tmp_path):
        manifest_path, tla_dir = holdout_corpus
        monkeypatch.setattr(cp, "_canonical_spec_path", lambda n: tla_dir / f"{n}.tla")
        result = cp.tag_corpus([survivor_dir], manifest_path)
        assert "survivor_family_counts" in result
        assert "holdout_family_counts" in result
        assert "family_overlap" in result
        assert isinstance(result["family_overlap"], list)

    def test_tag_corpus_empty_dirs_robust(self, empty_survivor_dir, holdout_corpus, monkeypatch):
        manifest_path, tla_dir = holdout_corpus
        monkeypatch.setattr(cp, "_canonical_spec_path", lambda n: tla_dir / f"{n}.tla")
        result = cp.tag_corpus([empty_survivor_dir], manifest_path)
        assert result["survivor_family_counts"] == {}


# ---------------------------------------------------------------------------
# Harmony SFT formatter
# ---------------------------------------------------------------------------

class TestHarmonySft:
    def test_final_channel_wraps_target(self):
        row = _mk_survivor_row("seed_x", "Write a spec for a bounded queue.", TRIVIAL_SPEC)
        out = cp.to_harmony_sft(row)
        assert "text" in out
        text = out["text"]
        # The critical property: assistant target lives in the FINAL channel.
        assert "<|channel|>final<|message|>" in text
        start = text.index("<|channel|>final<|message|>") + len("<|channel|>final<|message|>")
        end = text.index("<|return|>", start)
        final_payload = text[start:end]
        assert "```tla" in final_payload
        assert "MODULE Trivial" in final_payload
        assert "```cfg" in final_payload
        # user content must precede the assistant final channel
        user_idx = text.index("<|start|>user<|message|>")
        assert user_idx < start

    def test_metadata_fields_present(self):
        row = _mk_survivor_row("seed_y", "nl text", RICH_SPEC)
        row["seed_key"] = "seed_y"
        out = cp.to_harmony_sft(row)
        assert out["seed_key"] == "seed_y"
        assert out["family"] in cp.TAXONOMY_ORDER

    def test_build_sft_file_writes_jsonl(self, survivor_dir, tmp_path):
        out_path = tmp_path / "sft.jsonl"
        n = cp.build_sft_file([survivor_dir], out_path)
        assert n == 2
        lines = out_path.read_text().strip().splitlines()
        assert len(lines) == 2
        for line in lines:
            obj = json.loads(line)
            assert "text" in obj
            assert "seed_key" in obj
            assert "family" in obj

    def test_build_sft_file_tags_arm_without_min_tier(self, survivor_dir, tmp_path):
        """The Gate-2 pre-registration stratifies on "arm", so every rendered row
        must carry it -- including on the documented harvest command, which passes
        no --min-tier. Grading used to run only under a tier filter, so the default
        path emitted untaggable rows and a pooled number could hide a liveness
        regression."""
        out_path = tmp_path / "sft.jsonl"
        n = cp.build_sft_file([survivor_dir], out_path)
        rows = [json.loads(l) for l in out_path.read_text().strip().splitlines()]
        assert len(rows) == n
        for obj in rows:
            assert obj["arm"] in ("safety", "liveness")
            assert "tier_name" in obj

    def test_build_sft_file_min_tier_zero_is_a_no_op(self, survivor_dir, tmp_path):
        """--min-tier 0 keeps every tier, so it must not change the row set. It
        previously changed the *schema*, which is how the missing arm tag hid."""
        plain = tmp_path / "plain.jsonl"
        floored = tmp_path / "floored.jsonl"
        cp.build_sft_file([survivor_dir], plain)
        cp.build_sft_file([survivor_dir], floored, min_tier=0)
        assert plain.read_text() == floored.read_text()

    def test_build_sft_file_empty_dirs_robust(self, empty_survivor_dir, tmp_path):
        out_path = tmp_path / "sft_empty.jsonl"
        n = cp.build_sft_file([empty_survivor_dir], out_path)
        assert n == 0
        assert out_path.exists()
        assert out_path.read_text() == ""


# ---------------------------------------------------------------------------
# Row loading robustness
# ---------------------------------------------------------------------------

def test_load_survivors_skips_non_survived(tmp_path):
    d = tmp_path / "mixed"
    d.mkdir()
    rows = [
        _mk_survivor_row("s1", "nl", TRIVIAL_SPEC),
        {**_mk_survivor_row("s2", "nl", TRIVIAL_SPEC), "survived": False},
    ]
    with open(d / "w2_survivors.jsonl", "w") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")
    loaded = cp.load_survivors([d])
    assert len(loaded) == 1
    assert loaded[0]["seed_key"] == "s1"


def test_load_survivors_missing_file_robust(tmp_path):
    d = tmp_path / "no_file_here"
    d.mkdir()
    assert cp.load_survivors([d]) == []


def test_load_survivors_glob_dirs(tmp_path):
    d1 = tmp_path / "run_a"
    d1.mkdir()
    d2 = tmp_path / "run_b"
    d2.mkdir()
    for d, key in ((d1, "a1"), (d2, "b1")):
        with open(d / "w2_survivors.jsonl", "w") as f:
            f.write(json.dumps(_mk_survivor_row(key, "nl", TRIVIAL_SPEC)) + "\n")
    loaded = cp.load_survivors([tmp_path / "run_*"])
    keys = {r["seed_key"] for r in loaded}
    assert keys == {"a1", "b1"}
