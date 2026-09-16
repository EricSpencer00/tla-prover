"""Proof scaffold whitespace must survive stripped model extraction."""
import importlib.util
from pathlib import Path

import pytest


MODULE_PATH = Path(__file__).resolve().parents[1] / "tools/proof_dev_manifest.py"
SPEC = importlib.util.spec_from_file_location("proof_dev_manifest", MODULE_PATH)
builder = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(builder)


@pytest.mark.parametrize("fragment", [
    "    BY DEF Init, TypeOK\n",
    "\tBY DEFS TypeOK, lb, max\r\n",
    "  BY Foo, Bar\n    DEF Init, Next\n",
    "BY DEF Init, Next",
])
def test_boundary_move_preserves_exact_bytes(fragment):
    prefix = "<1>1. Init => TypeOK\n"
    suffix = "<1> QED BY <1>1\n"
    before = prefix + fragment + suffix
    p, f, s = builder.freeze_fragment_boundaries(prefix, fragment, suffix)
    assert p + f + s == before
    assert f == f.strip()
    if fragment.endswith("\n"):
        assert s.startswith("\n") or s.startswith("\r\n")


def test_stripped_generated_fragment_cannot_eat_newline():
    p, _, s = builder.freeze_fragment_boundaries("<1>1. Init => TypeOK\n", "  BY DEF Init, TypeOK\n", "<1> QED BY <1>1\n")
    candidate = p + "BY SMT DEF Init, TypeOK".strip() + s
    assert "TypeOK\n<1> QED" in candidate
    assert "\n  BY SMT" in candidate


@pytest.mark.parametrize("fragment", ["", " \n\t"])
def test_empty_fragment_rejected(fragment):
    with pytest.raises(ValueError, match="empty proof fragment"):
        builder.freeze_fragment_boundaries("prefix", fragment, "suffix")
