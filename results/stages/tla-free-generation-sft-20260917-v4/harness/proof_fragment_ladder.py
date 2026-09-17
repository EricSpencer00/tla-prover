"""SANY-first, exact-byte fragment ladder for free-generation outputs.

This is the legacy proof-hole contract with the repository's frozen SANY-first
ordering and one shared deadline.  A SANY rejection never reaches TLAPS, and
only an independently classified strict TLAPS proof can be certified.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
import shutil
import tempfile
import time

from . import proof_fragment_check as legacy
from . import proof_ladder_check as ladder
from . import runner
from tools.proof_outcome_audit import classify_outcome


VERSION = "sany-strict-tlaps-fragment-v1"


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _checked(path: Path, expected: str) -> bytes:
    raw = Path(path).read_bytes()
    if sha(raw) != expected:
        raise ValueError("exact source/candidate artifact changed")
    return raw


def _audit_tlaps(record: dict, prefix: str, fragment: str, suffix: str,
                 theorem_name: str, dependencies: dict) -> None:
    candidate = prefix + fragment + suffix
    expected = sha(candidate.encode())
    path = Path(record["candidate_path"])
    work = Path(record["workdir"])
    command = record.get("command", [])
    if (record.get("sha256") != expected or path.parent.resolve() != work.resolve()
            or path.name != command[-1] or Path(command[0]).resolve() != Path(runner.TLAPM).resolve()
            or not {"--strict", "--nofp"}.issubset(command)):
        raise ValueError("strict TLAPS provenance does not bind exact input")
    _checked(path, expected)
    if json.loads((work / "input.json").read_text()) != dict(
            prefix=prefix, fragment=fragment, suffix=suffix, theorem_name=theorem_name):
        raise ValueError("TLAPS raw input changed")
    if (work / "tlapm.log").read_text() != record.get("output", ""):
        raise ValueError("TLAPS raw log changed")
    for name, value in dependencies.items():
        _checked(work / name, value)
    if legacy.classify_result(record["returncode"], record["output"], record["timed_out"]) != (
            record["status"], record["proved"], record["total"]):
        raise ValueError("TLAPS raw outcome classification differs")
    if json.loads((work / "result.json").read_text()) != record:
        raise ValueError("TLAPS saved result differs")


def certify_fragment(prefix: str, fragment: str, suffix: str, *, theorem_name: str,
                     dependencies=(), work_root: Path, timeout=30,
                     run_command=None, tlaps_checker=None, clock=None) -> dict:
    if type(timeout) not in (int, float) or not math.isfinite(timeout) or not 0 < timeout <= 30:
        raise ValueError("one positive finite deadline of at most 30 seconds required")
    clock = clock or time.monotonic
    run_command = run_command or runner.run_cmd
    tlaps_checker = tlaps_checker or legacy.certify_fragment
    started = clock()
    root = Path(work_root).resolve()
    root.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="proof-fragment-ladder-", dir=root))
    candidate = (prefix + fragment + suffix).encode()
    result = {
        "contract_version": VERSION, "certified": False, "status": "contract_reject",
        "reason": "", "workdir": str(work), "sha256": sha(candidate),
        "timeout_seconds": timeout, "seconds": 0.0, "tlaps": None,
        "sany": {"status": "not_run", "command": None, "returncode": None,
                 "output": "", "seconds": 0.0, "timed_out": False},
    }
    (work / "input.json").write_text(json.dumps({
        "prefix": prefix, "fragment": fragment, "suffix": suffix,
        "theorem_name": theorem_name, "contract_version": VERSION}, indent=2))
    (work / "sany.log").write_text("")
    try:
        name = legacy.validate_fragment(prefix, fragment, suffix, theorem_name)
        path = work / (name + ".tla")
        path.write_bytes(candidate)
        seen = {path.name}
        dependency_hashes = {}
        dependency_sources = {}
        copies = []
        for dependency in dependencies:
            dependency = Path(dependency)
            if dependency.suffix != ".tla" or dependency.name in seen:
                raise ValueError("duplicate or non-TLA dependency")
            raw = dependency.read_bytes()
            if legacy.re.search(r"\b(?:THEOREM|LEMMA|COROLLARY|PROPOSITION|AXIOM)\b",
                                legacy._code(raw.decode())):
                raise ValueError("custom dependency exports unverified theorem or axiom declarations")
            seen.add(dependency.name)
            dependency_hashes[dependency.name] = sha(raw)
            dependency_sources[str(dependency.resolve())] = sha(raw)
            copy = work / dependency.name
            copy.write_bytes(raw)
            copies.append(copy)
        result.update(dependency_sha256=dependency_hashes,
                      dependency_source_sha256=dependency_sources,
                      candidate_path=str(path))
        java = shutil.which("java")
        if java is None:
            raise OSError("Java executable unavailable")
        java = str(Path(java).resolve())
        jar = Path(runner.TLA2TOOLS).resolve()
        if Path(runner.CLASSPATH).resolve() != jar:
            raise OSError("SANY classpath differs from pinned tla2tools JAR")
        jtmp = work / "jtmp"
        jtmp.mkdir()
        command = [java, "-Djava.io.tmpdir=" + str(jtmp),
                   "-DTLA-Library=" + runner.TLA_LIBRARY, "-cp", runner.CLASSPATH,
                   "tla2sany.SANY", path.name]
        result["sany"].update(command=command, java_path=java,
                               java_executable_sha256=sha(Path(java).read_bytes()),
                               jar_path=str(jar), jar_sha256=sha(jar.read_bytes()),
                               library_path=runner.TLA_LIBRARY)
        remaining = timeout - (clock() - started)
        if remaining <= 0:
            result["sany"]["status"] = "unmeasured_budget"
            result["status"] = "unmeasured_budget"
            return result
        rc, output, elapsed, timed_out = run_command(command, work, remaining)
        sany_status = ladder.classify_sany(rc, output, timed_out, name)
        result["sany"].update(status=sany_status, returncode=rc, output=output,
                               seconds=elapsed, timed_out=timed_out)
        (work / "sany.log").write_text(output)
        _checked(path, result["sha256"])
        for source, value in dependency_sources.items():
            _checked(Path(source), value)
        for copy in copies:
            _checked(copy, dependency_hashes[copy.name])
        if sany_status != "pass":
            result["status"] = sany_status
            return result
        remaining = timeout - (clock() - started)
        if remaining <= 0:
            result["status"] = "unmeasured_budget"
            return result
        tlaps = tlaps_checker(prefix, fragment, suffix, theorem_name=theorem_name,
                              dependencies=tuple(copies), work_root=work / "tlaps",
                              timeout=remaining)
        result["tlaps"] = tlaps
        _audit_tlaps(tlaps, prefix, fragment, suffix, theorem_name, dependency_hashes)
        diagnostic = classify_outcome(tlaps, provenance_verified=True)
        result["tlaps_diagnostic"] = diagnostic
        result["certified"] = bool(
            diagnostic.get("classification") == "proof_success"
            and tlaps.get("certified") is True and tlaps.get("status") == "pass"
            and tlaps.get("proved") == tlaps.get("total") > 0)
        result["status"] = "pass" if result["certified"] else diagnostic.get("classification", "tlaps_not_certified")
    except (OSError, RuntimeError) as exc:
        result.update(status="unmeasured_infrastructure", reason=str(exc))
    except (ValueError, KeyError, TypeError) as exc:
        result.update(status="contract_reject" if result["sany"]["status"] == "not_run"
                      else "unmeasured_provenance", reason=str(exc))
    except Exception as exc:
        result.update(status="unmeasured_unknown", reason=type(exc).__name__ + ": " + str(exc))
    finally:
        result["seconds"] = clock() - started
        (work / "result.json").write_text(json.dumps(result, indent=2))
    return result
