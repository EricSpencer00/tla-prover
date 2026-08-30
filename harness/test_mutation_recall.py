"""Tests for the mutation-operator recall gate (harness.mutation_recall).

The gate exists because the deployed battery is known low-recall: the 2026-07-21
no_kill spot-audit found 10 of 12 sampled no_kill rows had a real invariant that
a guard-removal mutant would violate, and the battery never generates it. The
two live tests at the bottom are the positive control -- they must show the gate
detecting exactly that miss on a spec built to have it, otherwise the gate has
no power and a passing recall number means nothing.
"""
from pathlib import Path

from harness.mutation_recall import (checked_names, comment_mask, probe_bound_shift,
                                     probe_cmp_relax, probe_guard_relax, probe_mutants,
                                     recall_row, run_probe_on_module, sample_rows,
                                     summarize_recall)
from harness.mutation import run_mutation_on_module


def _sites(fn, text, protect=()):
    from harness.mutation_recall import protect_checked
    mask = protect_checked(comment_mask(text), text, set(protect))
    return [text[s:e] for s, e, _ in fn(text, mask)]


# --- comment masking ---------------------------------------------------------
#
# A probe that lands in a comment produces a mutant that is textually different
# and semantically identical: it always survives, and every such survivor
# deflates recall for no reason.

def test_line_comment_is_masked():
    text = "x = 1\n\\* y < 2\nz = 3\n"
    mask = comment_mask(text)
    assert mask[text.index("y < 2")]
    assert not mask[text.index("z = 3")]


def test_block_comment_is_masked_and_nests():
    text = "a\n(* out (* in *) still *)\nb\n"
    mask = comment_mask(text)
    assert mask[text.index("still")]
    assert not mask[text.index("b\n")]


def test_probe_skips_commented_conjunct():
    text = "Act ==\n  /\\ x > 0\n\\*  /\\ y > 0\n"
    assert _sites(probe_guard_relax, text) == ["x > 0"]


# --- probe site selection ----------------------------------------------------

def test_guard_relax_finds_each_conjunct():
    text = "Act ==\n  /\\ x > 0\n  /\\ x' = x - 1\n"
    assert _sites(probe_guard_relax, text) == ["x > 0", "x' = x - 1"]


def test_guard_relax_skips_conjunct_with_a_continuation():
    # "x > 0" continues on the next, deeper-indented line; replacing only its
    # first line strands the continuation and buys a SANY failure, not evidence.
    # The deeper conjunct is itself complete, so it stays a site.
    text = "Act ==\n  /\\ x > 0\n       /\\ y > 0\n"
    assert _sites(probe_guard_relax, text) == ["y > 0"]


def test_guard_relax_skips_conjunct_already_true():
    assert _sites(probe_guard_relax, "Act ==\n  /\\ TRUE\n") == []


def test_cmp_relax_skips_lookalike_operators():
    # These are the tokens that forced mutation.py to DROP lt_to_le from the
    # deployed whole-file battery.
    text = "a << b >> c => d -> e ~> f |-> g <= h >= i\n"
    assert _sites(probe_cmp_relax, text) == []


def test_cmp_relax_finds_real_comparisons():
    assert _sites(probe_cmp_relax, "x < 2 /\\ y > 3\n") == ["<", ">"]


def test_bound_shift_increments_literals_only():
    text = "x1 = 2 /\\ y = 10\n"
    assert _sites(probe_bound_shift, text) == ["2", "10"]   # not the 1 in "x1"


def test_bound_shift_replacement_is_n_plus_one():
    text = "n = 9\n"
    mask = comment_mask(text)
    assert [r for _, _, r in probe_bound_shift(text, mask)] == ["10"]


# --- the checked property is off limits --------------------------------------

def test_checked_names_reads_invariant_and_property():
    cfg = "INIT Init\nNEXT Next\nINVARIANTS TypeOK, Safety\nPROPERTY Liveness\n"
    assert checked_names(cfg) == {"TypeOK", "Safety", "Liveness"}


def test_probes_never_touch_the_checked_definition():
    # Corrupting the invariant makes it violated by construction -- a kill that
    # says nothing about whether the spec catches a corruption.
    text = ("Act ==\n  /\\ x > 0\n  /\\ x' = x - 1\n\n"
            "Safety ==\n  /\\ x >= 0\n  /\\ x < 9\n")
    assert _sites(probe_guard_relax, text, protect={"Safety"}) == ["x > 0", "x' = x - 1"]
    assert "9" not in _sites(probe_bound_shift, text, protect={"Safety"})


def test_probe_mutants_labels_carry_the_operator():
    text = "Act ==\n  /\\ x > 0\n  /\\ x' = x - 1\n"
    labels = [lbl for lbl, m in probe_mutants(text) if m is not None]
    assert "guard_relax#0" in labels and "guard_relax#1" in labels


def test_probe_mutants_reports_operator_with_no_site_as_inapplicable():
    # Same convention as the deployed battery: no site is not a survived mutant.
    labels = dict(probe_mutants("Trivial == TRUE\n"))
    assert labels["cmp_relax"] is None


# --- recall arithmetic -------------------------------------------------------

def _mut(op, safety):
    return {"mutation": op, "safety_killed": safety}


def test_recall_row_covered_when_both_sets_kill():
    r = recall_row("s", {"safety_killed": 1, "attempted": 4},
                   {"safety_killed": 2, "attempted": 6,
                    "mutants": [_mut("guard_relax#0", True)]})
    assert r["verdict"] == "covered"


def test_recall_row_miss_when_only_the_probes_kill():
    r = recall_row("s", {"safety_killed": 0, "attempted": 0},
                   {"safety_killed": 1, "attempted": 6,
                    "mutants": [_mut("guard_relax#0", True), _mut("cmp_relax#0", False)]})
    assert r["verdict"] == "recall_miss"
    assert r["probe_killers"] == ["guard_relax"]


def test_recall_row_no_evidence_when_neither_kills():
    # Excluded from the denominator: the probes did not prove a catch is
    # possible, so the battery cannot be blamed for not finding one.
    r = recall_row("s", {"safety_killed": 0, "attempted": 4},
                   {"safety_killed": 0, "attempted": 6, "mutants": []})
    assert r["verdict"] == "no_evidence"


def test_summarize_recall_ok_above_floor():
    rows = [{"verdict": "covered", "probe_killers": []},
            {"verdict": "covered", "probe_killers": []},
            {"verdict": "recall_miss", "probe_killers": ["guard_relax"]},
            {"verdict": "no_evidence", "probe_killers": []}]
    rep = summarize_recall(rows, min_recall=0.5)
    assert rep["operator_recall"] == round(2 / 3, 2)
    assert rep["no_evidence"] == 1        # excluded from the denominator
    assert rep["missing_operators"] == {"guard_relax": 1}
    assert rep["ok"] is True


def test_summarize_recall_fails_below_floor_and_names_the_operators():
    rows = [{"verdict": "covered", "probe_killers": []},
            {"verdict": "recall_miss", "probe_killers": ["guard_relax"]},
            {"verdict": "recall_miss", "probe_killers": ["guard_relax", "cmp_relax"]}]
    rep = summarize_recall(rows, min_recall=0.5)
    assert rep["operator_recall"] == round(1 / 3, 2)
    assert rep["ok"] is False
    assert rep["missing_operators"] == {"guard_relax": 2, "cmp_relax": 1}
    assert "guard_relax" in rep["failures"][0]


def test_summarize_recall_fails_when_no_spec_gives_probe_evidence():
    # No power: every spec is no_evidence, so the gate cannot license any
    # reading of mutation_evidence and must not report a green recall.
    rep = summarize_recall([{"verdict": "no_evidence", "probe_killers": []}] * 3)
    assert rep["operator_recall"] is None
    assert rep["ok"] is False


def test_summarize_recall_fails_on_empty_input():
    assert summarize_recall([])["ok"] is False


def test_sample_rows_is_reproducible_and_keeps_ledger_order():
    rows = [{"i": i} for i in range(20)]
    a = sample_rows(rows, 5, seed=7)
    assert a == sample_rows(rows, 5, seed=7)
    assert len(a) == 5
    assert [r["i"] for r in a] == sorted(r["i"] for r in a)


def test_sample_rows_returns_everything_under_the_limit():
    rows = [{"i": i} for i in range(3)]
    assert sample_rows(rows, 10) == rows


# --- positive control: the gate detects a real battery miss ------------------
#
# Vault's only guard is "bal > 0". Removing it walks bal below zero and trips
# NonNegative. NONE of the four deployed operators applies (no \in, no \cup, no
# plus_to_minus site; and_to_or only makes TLC crash), so the ledger records
# no_site -- the exact reading the audit says is unreadable. The probes must
# kill it.

_VAULT = """---- MODULE Vault ----
EXTENDS Integers
VARIABLE bal
Init == bal = 3
Wd ==
  /\\ bal > 0
  /\\ bal' = bal - 1
Next == Wd
NonNegative == bal >= 0
====
"""
_VAULT_CFG = "INIT Init\nNEXT Next\nINVARIANT NonNegative\n"

# Cap keeps a \in site, so the deployed battery does score a safety kill here.
_CAP = """---- MODULE Cap ----
EXTENDS Integers
VARIABLE bal
Init == bal = 0
Up ==
  /\\ bal \\in {0, 1}
  /\\ bal' = bal + 1
Next == Up
Bounded == bal \\in 0..2
====
"""
_CAP_CFG = "INIT Init\nNEXT Next\nINVARIANT Bounded\n"


def _score(tmp_path: Path, name: str, spec: str, cfg: str) -> dict:
    d = tmp_path / name
    d.mkdir()
    tla = d / f"{name}.tla"
    tla.write_text(spec)
    (d / f"{name}.cfg").write_text(cfg)
    battery = run_mutation_on_module(tla, cfg, name, timeout=60)
    probe = run_probe_on_module(tla, cfg, name, timeout=60)
    return recall_row(name, battery, probe)


def test_battery_miss_is_reported_as_recall_miss(tmp_path):
    r = _score(tmp_path, "Vault", _VAULT, _VAULT_CFG)
    assert r["battery_safety_killed"] == 0
    assert r["probe_safety_killed"] > 0
    assert r["verdict"] == "recall_miss"
    assert "guard_relax" in r["probe_killers"]


def test_spec_the_battery_does_reach_is_reported_as_covered(tmp_path):
    r = _score(tmp_path, "Cap", _CAP, _CAP_CFG)
    assert r["battery_safety_killed"] > 0
    assert r["probe_safety_killed"] > 0
    assert r["verdict"] == "covered"
