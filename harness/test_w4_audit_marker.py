"""The floors-met marker file must actually get written.

The audit documented exit 10 as "write W4_FLOOR_REACHED.md" for weeks while no
code path created it, so any downstream check for the file never fired.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from tools.w4_audit import write_marker  # noqa: E402


def test_write_marker_creates_file(tmp_path):
    path = tmp_path / "W4_FLOOR_REACHED.md"
    assert write_marker(["total 5010/5000 MET", "STOP=YES"], path) is True
    text = path.read_text()
    assert "STOP=YES" in text
    assert "total 5010/5000 MET" in text


def test_write_marker_keeps_existing_notes(tmp_path):
    path = tmp_path / "W4_FLOOR_REACHED.md"
    path.write_text("hand-written\n")
    assert write_marker(["STOP=YES"], path) is False
    assert path.read_text() == "hand-written\n"
