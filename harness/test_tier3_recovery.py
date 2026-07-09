from pathlib import Path

from .tier3_recovery import (
    cfg_identifiers,
    cfg_matches_module,
    find_matching_sibling_cfg,
    missing_module_names,
    parse_module,
    template_cfg_for_module,
    template_cfg_symmetric_sets,
)

MOD_WITH_SPEC = """
---------------------------- MODULE Foo ----------------------------
EXTENDS Naturals
CONSTANT N, Procs
VARIABLES x, y

TypeOK == x \\in Nat

Init == /\\ x = 0 /\\ y = {}
Next == x' = x + 1 /\\ y' = y
Spec == Init /\\ [][Next]_<<x,y>>
=============================================================================
"""

MOD_NO_SPEC_INIT_NEXT = """
---------------------------- MODULE Bar ----------------------------
CONSTANT K
Init == TRUE
Next == TRUE
=============================================================================
"""

MOD_NOTHING = """
---------------------------- MODULE Baz ----------------------------
CONSTANT X
Foo == X
=============================================================================
"""


def test_parse_module_basic():
    facts = parse_module(MOD_WITH_SPEC)
    assert facts["module"] == "Foo"
    assert facts["constants"] == ["N", "Procs"]
    assert facts["variables"] == ["x", "y"]
    assert facts["has_spec"]
    assert facts["invariant_name"] == "TypeOK"


def test_parse_module_no_spec_falls_back_to_init_next():
    facts = parse_module(MOD_NO_SPEC_INIT_NEXT)
    assert not facts["has_spec"]
    assert facts["has_init"] and facts["has_next"]


def test_template_cfg_uses_spec_when_present():
    cfg = template_cfg_for_module(MOD_WITH_SPEC)
    assert cfg is not None
    assert "SPECIFICATION Spec" in cfg
    assert "INVARIANT TypeOK" in cfg
    # N looks like a small-int constant, Procs looks like a set constant
    assert "CONSTANT N = 3" in cfg
    assert "CONSTANT Procs = {Procs_v1, Procs_v2, Procs_v3}" in cfg


def test_template_cfg_falls_back_to_init_next():
    cfg = template_cfg_for_module(MOD_NO_SPEC_INIT_NEXT)
    assert cfg is not None
    assert "INIT Init" in cfg and "NEXT Next" in cfg
    assert "CONSTANT K = 3" in cfg


def test_template_cfg_none_when_nothing_to_check():
    assert template_cfg_for_module(MOD_NOTHING) is None


def test_template_cfg_symmetric_sets_reports_bound_constants():
    cfg, bound = template_cfg_symmetric_sets(MOD_WITH_SPEC)
    assert bound == ["N", "Procs"]
    assert "CONSTANT Procs = {Procs_v1, Procs_v2, Procs_v3}" in cfg


def test_cfg_identifiers_parses_multiple_keywords():
    cfg = "SPECIFICATION Spec\nINVARIANT TypeOK Safety\n"
    assert cfg_identifiers(cfg) == {"Spec", "TypeOK", "Safety"}


def test_cfg_matches_module_true_when_all_defined():
    cfg = "SPECIFICATION Spec\nINVARIANT TypeOK\n"
    assert cfg_matches_module(cfg, MOD_WITH_SPEC)


def test_cfg_matches_module_false_when_mismatched():
    cfg = "SPECIFICATION Spec\nINVARIANT NotDefinedAnywhere\n"
    assert not cfg_matches_module(cfg, MOD_WITH_SPEC)


def test_cfg_matches_module_false_when_empty():
    assert not cfg_matches_module("", MOD_WITH_SPEC)


def test_find_matching_sibling_cfg_swaps_when_original_mismatched(tmp_path):
    d = tmp_path
    used = d / "Wrong.cfg"
    used.write_text("SPECIFICATION Spec\nINVARIANT NotDefinedAnywhere\n")
    good = d / "Right.cfg"
    good.write_text("SPECIFICATION Spec\nINVARIANT TypeOK\n")
    result = find_matching_sibling_cfg(MOD_WITH_SPEC, used, [used, good])
    assert result == good


def test_find_matching_sibling_cfg_none_when_original_already_matches(tmp_path):
    d = tmp_path
    used = d / "Used.cfg"
    used.write_text("SPECIFICATION Spec\nINVARIANT TypeOK\n")
    other = d / "Other.cfg"
    other.write_text("SPECIFICATION Spec\nINVARIANT TypeOK\n")
    result = find_matching_sibling_cfg(MOD_WITH_SPEC, used, [used, other])
    assert result is None


def test_find_matching_sibling_cfg_none_when_no_candidate_matches(tmp_path):
    d = tmp_path
    used = d / "Used.cfg"
    used.write_text("SPECIFICATION Spec\nINVARIANT Nope\n")
    other = d / "Other.cfg"
    other.write_text("SPECIFICATION Spec\nINVARIANT AlsoNope\n")
    result = find_matching_sibling_cfg(MOD_WITH_SPEC, used, [used, other])
    assert result is None


def test_missing_module_names_extracts_source_file_error():
    err = "Cannot find source file for module 'FooBar'\n***Parse Error***"
    assert missing_module_names(err) == ["FooBar"]


def test_missing_module_names_extracts_unknown_operator():
    err = "***Parse Error*** Unknown operator `BazQux`"
    assert missing_module_names(err) == ["BazQux"]


def test_missing_module_names_empty_when_no_match():
    assert missing_module_names("Model checking completed. No error has been found.") == []
