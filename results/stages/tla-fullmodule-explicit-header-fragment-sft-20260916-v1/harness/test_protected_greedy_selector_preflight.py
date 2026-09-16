import sys
import pytest

from tools import protected_greedy_selector_preflight as probe


def test_changed_input_fails_before_runtime_or_output(tmp_path, monkeypatch):
    wrong = tmp_path / 'wrong'
    wrong.write_text('not the frozen grammar')
    output = tmp_path / 'receipt.json'
    monkeypatch.setattr(sys, 'argv', ['probe', '--grammar', str(wrong), '--corpus', str(wrong),
        '--model', str(wrong), '--xgrammar-site', str(wrong), '--output', str(output)])
    with pytest.raises(ValueError, match='Exact inputs'):
        probe.main()
    assert not output.exists()
