import json
from pathlib import Path
import sys

import pytest

from harness import proof_fragment_ladder as ladder


PREFIX = "---- MODULE M ----\nTHEOREM T == TRUE\n"
SUFFIX = "\n====\n"


@pytest.fixture
def runtime(tmp_path, monkeypatch):
    jar = tmp_path / "tla2tools.jar"
    jar.write_bytes(b"pinned jar")
    monkeypatch.setattr(ladder.runner, "TLA2TOOLS", jar)
    monkeypatch.setattr(ladder.runner, "CLASSPATH", str(jar))
    monkeypatch.setattr(ladder.shutil, "which", lambda name: sys.executable)
    return tmp_path


def fake_tlaps(prefix, fragment, suffix, *, theorem_name, dependencies, work_root, timeout):
    work_root.mkdir(parents=True)
    path = work_root / "M.tla"
    path.write_text(prefix + fragment + suffix)
    output = "[INFO]: All 1 obligations proved.\n"
    record = dict(certified=True, status="pass", proved=1, total=1, returncode=0,
                  timed_out=False, output=output, seconds=1.0,
                  workdir=str(work_root), candidate_path=str(path),
                  sha256=ladder.sha(path.read_bytes()), dependency_sha256={},
                  command=[str(ladder.runner.TLAPM), "--strict", "--nofp", "M.tla"])
    (work_root / "input.json").write_text(json.dumps(dict(
        prefix=prefix, fragment=fragment, suffix=suffix, theorem_name=theorem_name)))
    (work_root / "tlapm.log").write_text(output)
    (work_root / "result.json").write_text(json.dumps(record))
    return record


def test_sany_reject_never_calls_tlaps(runtime):
    def no_tlaps(*args, **kwargs):
        raise AssertionError("TLAPS must not run after SANY rejection")

    result = ladder.certify_fragment(
        PREFIX, "BY SMT", SUFFIX, theorem_name="T", work_root=runtime / "run",
        run_command=lambda *args: (1, "Semantic errors:\n*** Errors: 1\n", 1.0, False),
        tlaps_checker=no_tlaps)
    assert result["sany"]["status"] == "model_sany_reject"
    assert result["tlaps"] is None
    assert not result["certified"]


def test_shared_sany_tlaps_deadline_and_exact_input(runtime):
    now = [0.0]
    calls = []

    def sany(command, work, timeout):
        calls.append(("sany", timeout))
        now[0] += 2
        assert (work / "M.tla").read_text() == PREFIX + "BY SMT" + SUFFIX
        return 0, "Semantic processing of module M\n", 2.0, False

    def tlaps(*args, **kwargs):
        calls.append(("tlaps", kwargs["timeout"]))
        now[0] += 2
        return fake_tlaps(*args, **kwargs)

    result = ladder.certify_fragment(
        PREFIX, "BY SMT", SUFFIX, theorem_name="T", work_root=runtime / "run",
        run_command=sany, tlaps_checker=tlaps, clock=lambda: now[0])
    assert result["certified"] and result["status"] == "pass"
    assert calls == [("sany", 30), ("tlaps", 28)]
    assert json.loads((Path(result["workdir"]) / "result.json").read_text()) == result


def test_current_development_scaffold_uses_fragment_contract():
    manifest = json.loads(Path("results/runs/proof-free-generation-sft-20260917-v3/manifest.json").read_text())
    task = next(row for row in manifest["tasks"] if row["split"] == "development")
    with pytest.raises(ValueError, match="whole-proof boundaries"):
        # The whole-proof ladder must not silently replace the legacy fragment
        # contract used by this branch; this test documents the distinction.
        from harness import proof_ladder_check
        proof_ladder_check.full.validate_fragment(task["prefix"], "BY DEF TypeOK",
                                                  task["suffix"], task["theorem_name"])
