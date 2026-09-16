"""W2.4 proof-trace bootstrap (PLAN.md Amendment 8).

Runs tlapm in --toolbox --printallobs mode over TLAPS proof modules and
harvests one JSONL row per obligation: which module/theorem it came from,
its normalized goal text, which backend discharged it (if any), and the
final status. --toolbox mode emits a stream of

    @!!BEGIN
    @!!type:obligation
    @!!id:<int>
    @!!loc:<l1>:<c1>:<l2>:<c2>
    @!!status:<to be proved|normalized|proved|failed|...>
    @!!prover:<zenon|smt|isabelle|...>        (only on backend-result blocks)
    @!!meth:<...>                             (only on backend-result blocks)
    @!!obl:<obligation text, possibly multi-line>
    @!!END

blocks -- this module parses that stream directly rather than re-deriving it
from tlapm's human-readable summary, since the toolbox blocks are the only
place obligation text and per-backend timing are both present (studied via
harness/proof_tools.py's ProofSmoke.tla fixture + real corpus spec 67 before
writing this parser; see PLAN.md W2.4 report for the raw transcript).

Each obligation id can appear in multiple blocks as tlapm re-emits it (first
"to be proved", then "normalized", then one block per backend attempt). The
row we keep per obligation is the LAST block with a terminal status (proved/
failed) if one exists, else the last block seen (still "to be proved" means
tlapm never got to it -- recorded as status="unattempted").
"""
import json
import re
import shutil
import time
from pathlib import Path

from .runner import REPO, TLAPM, TLA_LIBRARY, run_cmd, module_name as _module_name_of

TERMINAL_STATUSES = {"proved", "failed"}

THEOREM_RE = re.compile(
    r"^\s*(THEOREM|LEMMA|COROLLARY|PROPOSITION)\s+(?:([A-Za-z_]\w*)\s*==)?", re.M)

BLOCK_RE = re.compile(r"@!!BEGIN\n(.*?)@!!END", re.S)


def _parse_block(block_text):
    """One @!!BEGIN..@!!END block -> dict of its @!!key:value fields. The
    @!!obl field is multi-line free text (goal term) so it is handled specially:
    everything after '@!!obl:' up to the next '@!!' line or block end."""
    fields = {}
    lines = block_text.split("\n")
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("@!!obl:"):
            obl_lines = [line[len("@!!obl:"):]]
            i += 1
            while i < len(lines) and not lines[i].startswith("@!!"):
                obl_lines.append(lines[i])
                i += 1
            fields["obl"] = "\n".join(obl_lines).strip()
            continue
        if line.startswith("@!!"):
            rest = line[3:]
            if ":" in rest:
                k, v = rest.split(":", 1)
                fields[k] = v.strip()
        i += 1
    return fields


def parse_toolbox_stream(out: str):
    """--toolbox --printallobs stdout -> list of per-obligation dicts:
    {id, loc, obl, status, prover, meth}. `status`/`prover`/`meth` reflect
    the LAST terminal (proved/failed) block for that id, else the last block
    seen (status possibly still 'to be proved' -> normalized to 'unattempted'
    by the caller). `obl` is the fullest (longest, i.e. least-normalized-away)
    text seen across all blocks for that id."""
    by_id = {}
    for m in BLOCK_RE.finditer(out):
        f = _parse_block(m.group(1))
        if f.get("type") != "obligation" or "id" not in f:
            continue
        oid = f["id"]
        prev = by_id.get(oid)
        if prev is None:
            by_id[oid] = dict(f)
            continue
        # keep the longest obl text seen so far (later blocks sometimes omit it)
        if len(f.get("obl", "")) > len(prev.get("obl", "")):
            prev_obl = f.get("obl")
        else:
            prev_obl = prev.get("obl", "")
        # a terminal status always wins over a non-terminal one; between two
        # terminal blocks (shouldn't normally happen) keep the later one.
        if f.get("status") in TERMINAL_STATUSES or prev.get("status") not in TERMINAL_STATUSES:
            merged = dict(f)
            merged["obl"] = prev_obl
            by_id[oid] = merged
        else:
            prev["obl"] = prev_obl
    return list(by_id.values())


def nearest_theorem_name(tla_text: str, line: int):
    """Best-effort attribution: the THEOREM/LEMMA/COROLLARY/PROPOSITION whose
    declaration line is the closest one at-or-before `line`. Returns
    (kind, name) with name=None for unnamed theorems (still valid TLA+)."""
    best = (None, None)
    best_line = -1
    for m in THEOREM_RE.finditer(tla_text):
        decl_line = tla_text.count("\n", 0, m.start()) + 1
        if decl_line <= line and decl_line > best_line:
            best_line = decl_line
            best = (m.group(1), m.group(2))
    return best


def extract_obligation_rows(tla_file: Path, workdir: Path, source: str, module_id: str,
                             timeout=600, orig_path: str = None):
    """Runs tlapm --toolbox --printallobs over tla_file (already copied into
    workdir with its deps) and returns (module_status, rows, raw_out, seconds).

    module_status: 'pass' (all obligations proved), 'partial' (some
    proved/failed), 'timeout', 'no_obligations' (SANY-clean file with 0
    THEOREM/LEMMA proof obligations), or 'error' (tlapm itself errored before
    producing any obligation blocks).

    rows: list of obligation-row dicts per the JSONL schema (see
    run_proof_traces docstring), source/module/mod_file fields already filled.
    """
    include_flags = []
    for p in TLA_LIBRARY.split(":"):
        include_flags += ["-I", p]
    rc, out, dt, timed_out = run_cmd(
        [str(TLAPM), "--toolbox", "0", "0", "--printallobs"] + include_flags
        + [tla_file.name], workdir, timeout)
    tla_text = tla_file.read_text(errors="replace")
    mod = _module_name_of(tla_text) or tla_file.stem

    if timed_out:
        return "timeout", [], out, dt

    obls = parse_toolbox_stream(out)
    if not obls:
        # SANY/parse failure or a proof-free module -- distinguish by whether
        # tlapm reported a module error.
        status = "error" if ("Fatal error" in out or rc not in (0, 1)) and "obligations proved" not in out \
            else "no_obligations"
        return status, [], out, dt

    rows = []
    n_proved = 0
    for o in obls:
        loc = o.get("loc", "")
        line1 = 0
        lm = re.match(r"(\d+):", loc)
        if lm:
            line1 = int(lm.group(1))
        kind, name = nearest_theorem_name(tla_text, line1) if line1 else (None, None)
        status = o.get("status", "unknown")
        if status == "to be proved" or status == "normalized":
            status = "unattempted"
        if status == "proved":
            n_proved += 1
        rows.append({
            "source": source,
            "module": mod,
            "module_path": orig_path if orig_path is not None else str(tla_file),
            "module_id": module_id,
            "theorem_kind": kind,
            "theorem_name": name,
            "obligation_id": o.get("id"),
            "loc": loc,
            "obligation_text": o.get("obl", ""),
            "backend": o.get("prover"),
            "method": o.get("meth"),
            "status": status,
        })

    if n_proved == len(rows):
        mstatus = "pass"
    elif n_proved == 0:
        mstatus = "fail"
    else:
        mstatus = "partial"
    return mstatus, rows, out, dt


def run_proof_traces(out_dir: Path, source: str, modules, timeout=600):
    """modules: list of (module_id, tla_path, dep_paths) tuples; dep_paths are
    corpus-local/example-local sibling .tla files to stage alongside tla_path
    in a scratch workdir (tlapm resolves EXTENDS/INSTANCE relative to cwd plus
    -I search path; corpus siblings are not on -I, so they must be copied).

    Writes out_dir/rows.jsonl (Rule 8, append-only across calls: existing rows
    for a module_id are left in place and re-attempted modules just append —
    callers that want a clean rerun should pass a fresh out_dir), out_dir/
    config.json, and returns the summary dict (also written to
    out_dir/summary.json by the CLI entry point, not here, so repeated calls
    in tests don't clobber a caller's own summary timing)."""
    out_dir.mkdir(parents=True, exist_ok=True)
    rows_path = out_dir / "rows.jsonl"
    module_rows = []
    scratch_root = out_dir / "_scratch"

    for module_id, tla_path, dep_paths in modules:
        tla_path = Path(tla_path)
        work = scratch_root / module_id
        if work.exists():
            shutil.rmtree(work)
        work.mkdir(parents=True)
        # tlapm resolves EXTENDS/INSTANCE by MODULE name, not by filename --
        # corpus files are named by spec number (e.g. 65.tla holds "MODULE
        # EWD840"), so both the main file and every dep must be staged under
        # their internal module name or a dependent EXTENDS fails with
        # "Unknown module" even though the file is present (found empirically
        # 2026-07-08: corpus specs 67/112/131/137/139/142 all errored this way
        # on the first sweep before this fix).
        main_text = tla_path.read_text(errors="replace")
        main_name = _module_name_of(main_text) or tla_path.stem
        main_dest = work / f"{main_name}.tla"
        main_dest.write_text(main_text)
        for d in dep_paths:
            d = Path(d)
            dtext = d.read_text(errors="replace")
            dname = _module_name_of(dtext) or d.stem
            (work / f"{dname}.tla").write_text(dtext)
        t0 = time.time()
        mstatus, rows, out, dt = extract_obligation_rows(
            main_dest, work, source, module_id, timeout=timeout, orig_path=str(tla_path))
        (out_dir / f"{module_id}.tlapm.log").write_text(out)
        with open(rows_path, "a") as fh:
            for r in rows:
                fh.write(json.dumps(r) + "\n")
        module_rows.append({
            "module_id": module_id, "module_path": str(tla_path),
            "status": mstatus, "obligations": len(rows),
            "proved": sum(1 for r in rows if r["status"] == "proved"),
            "seconds": round(dt, 1),
        })
        shutil.rmtree(work, ignore_errors=True)

    shutil.rmtree(scratch_root, ignore_errors=True)
    return summarize(module_rows)


def summarize(module_rows):
    by_backend = {}
    total_obl = proved = 0
    for m in module_rows:
        total_obl += m["obligations"]
        proved += m["proved"]
    return {
        "modules_attempted": len(module_rows),
        "modules_status": {
            s: sum(1 for m in module_rows if m["status"] == s)
            for s in sorted({m["status"] for m in module_rows})
        },
        "obligations_total": total_obl,
        "obligations_proved": proved,
        "module_rows": module_rows,
    }


def backend_discharge_rates(rows_path: Path):
    """Reads a rows.jsonl and returns {backend: {"proved": n, "total": n}} for
    obligations that reached a terminal status (proved/failed); 'unattempted'
    obligations (tlapm never got to them, e.g. an earlier sibling timed out
    the whole run) are excluded since they have no backend attempt to score."""
    counts = {}
    if not rows_path.exists():
        return counts
    with open(rows_path) as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            if r["status"] not in ("proved", "failed"):
                continue
            b = r.get("backend") or "unknown"
            c = counts.setdefault(b, {"proved": 0, "total": 0})
            c["total"] += 1
            if r["status"] == "proved":
                c["proved"] += 1
    return counts
