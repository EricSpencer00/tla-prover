from pathlib import Path
import sys

import pytest

from tools import protected_mask_cost_boundary as boundary
from tools.grammar_falsereject import make_checker


def test_timing_control_is_explicitly_not_a_syntax_verifier():
    accepts = make_checker(boundary.CONTROL)
    assert accepts('not TLA+\n\t[]{}')
    assert not accepts('\u2603')


def test_boundary_rejects_changed_payload_before_imports(tmp_path, monkeypatch):
    path = tmp_path / 'changed'
    path.write_text('wrong')
    monkeypatch.setattr(sys, 'argv', ['probe', '--grammar', str(path), '--corpus', str(path),
                                    '--model', str(path), '--xgrammar-site', str(path)])
    with pytest.raises(ValueError, match='Exact prior grammar/corpus'):
        boundary.main()
