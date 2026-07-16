"""E2.c Gate-2 baseline eval (PLAN Amendment 12).

Two framings over the frozen 30-spec holdout (corpus/holdout_30.json):
  A -- NL->spec generation: FormaLLM description -> model emits a TLA+ module,
       scored by the Amendment-1/3 population criterion (+ Rule 9 semaudit).
  B -- repair-from-standardized-corruption: one deterministic mutation per spec,
       model repairs it, same criterion.

This module holds the deterministic pieces (cfg-signature parse, prompt build,
response parse, pass@k). Model calls reuse harness.repair's Model classes;
scoring reuses harness.runner's oracle machinery.
"""
import hashlib
import json
import os
import random
import re
import shutil
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from .mutation import MUTATIONS
from .repair import make_model, verdict_of
from .runner import REPO, build_module_index, eval_module_text

DEFAULT_CORPUS = Path("/Users/eric/GitHub/tla_benchmark/data")
HOLDOUT_FILE = REPO / "corpus" / "holdout_30.json"
# Amendment 12 frozen budget (PLAN ledger entry 12): never inline these elsewhere.
TEMPERATURE = 0.8
MAX_TOKENS = 16384
TLC_TIMEOUT_S = 120

# GEN_EVAL_CONCURRENCY > 1 prefetches a spec's sample generations in parallel
# (vLLM batches concurrent requests near-linearly; the 2026-07-15 Gate-2 B
# re-run spent 11.2h of its 12.2h wall on strictly SERIAL model calls at 0.2%
# KV-cache use). Scoring order, row contents, temperatures, and the per-request
# model_s budget are unchanged -- this overlaps ONLY the network calls.
GEN_EVAL_CONCURRENCY = int(os.environ.get("GEN_EVAL_CONCURRENCY", "1"))


def _prefetch_replies(model, prompt, samples, done, num):
    """Return {sample_id: (reply, model_s)} for the samples not already in the
    resume ledger. Sequential when GEN_EVAL_CONCURRENCY==1 (frozen behavior);
    otherwise a thread pool fires the independent requests together."""
    todo = [(sid, t) for sid, t in samples if (num, sid) not in done]

    def _one(args):
        sid, temperature = args
        t0 = time.time()
        reply = model.generate(prompt, 1, temperature, MAX_TOKENS)[0]
        return sid, (reply, round(time.time() - t0, 1))

    if GEN_EVAL_CONCURRENCY <= 1 or len(todo) <= 1:
        return dict(_one(a) for a in todo)
    with ThreadPoolExecutor(max_workers=GEN_EVAL_CONCURRENCY) as pool:
        return dict(pool.map(_one, todo))

# TLC .cfg section keywords (subset we care about for the required signature).
_CFG_KEYWORDS = {
    "CONSTANT", "CONSTANTS", "SPECIFICATION", "INIT", "NEXT",
    "INVARIANT", "INVARIANTS", "PROPERTY", "PROPERTIES",
    "CONSTRAINT", "ACTION_CONSTRAINT", "SYMMETRY", "VIEW", "ALIAS",
    "CHECK_DEADLOCK", "POSTCONDITION",
}


def required_signature(cfg_text):
    """Parse a TLC .cfg into the identifiers a generated module must define:
    constants (names), specification (temporal formula name or None), init/next
    (names or None), invariants (list), properties (list). This is what the
    generation prompt tells the model to define, so the reference cfg can score
    its output."""
    sig = {"constants": [], "specification": None, "init": None, "next": None,
           "invariants": [], "properties": []}
    section = None
    for raw in cfg_text.splitlines():
        line = raw.split("\\*", 1)[0].strip()  # strip cfg comments
        if not line:
            continue
        head = line.split()[0]
        if head in _CFG_KEYWORDS:
            section = head
            rest = line[len(head):].strip()
            body = rest
        else:
            body = line
        if not body:
            continue
        if section in ("CONSTANT", "CONSTANTS"):
            # entries "Name = value" or "Name <- op"; take the left identifier
            name = re.split(r"<-|=", body, maxsplit=1)[0].strip()
            if name:
                sig["constants"].append(name)
        elif section == "SPECIFICATION":
            sig["specification"] = body.split()[0]
        elif section == "INIT":
            sig["init"] = body.split()[0]
        elif section == "NEXT":
            sig["next"] = body.split()[0]
        elif section in ("INVARIANT", "INVARIANTS"):
            sig["invariants"].extend(body.split())
        elif section in ("PROPERTY", "PROPERTIES"):
            sig["properties"].extend(body.split())
    return sig


_MODULE_RE = re.compile(r"^-{4,}\s*MODULE\b.*?^={4,}", re.S | re.M)


def extract_module(response):
    """Pull the first `---- MODULE ... ====` block out of a model response,
    tolerating markdown fences and surrounding prose. Returns the module text
    (fences stripped) or None if no complete module is present."""
    m = _MODULE_RE.search(response)
    return m.group(0).strip() if m else None


class NoCandidateMutation(Exception):
    """Raised by corrupt() when spec_text has no site where any MUTATIONS
    operator regex matches -- there is nothing to corrupt, so returning the
    text unchanged would silently make the repair task empty (forbidden by
    the E2.c handoff). Callers must catch this and exclude the spec from the
    Framing-B (repair) sample rather than treat it as a corrupted spec."""
    pass


def corrupt(spec_text, seed):
    """Option-B corruption: apply exactly ONE deterministic seeded mutation
    swap (reusing harness.mutation.MUTATIONS, the same SpecGen-style
    whole-module operator-swap regexes used by the mutation kill-rate tool)
    to spec_text, and return (corrupted_text, mutation_record).

    Determinism / seed convention: `seed` is an int chosen entirely by the
    CALLER (the orchestration step derives it from spec number + the frozen
    holdout hash -- this function does not know or care about that scheme).
    Given the same (spec_text, seed) this function always returns the same
    corrupted output.

    Site selection: for each MUTATIONS operator (in the fixed order they
    appear in mutation.MUTATIONS, which is itself fixed by that module), we
    scan spec_text for ALL non-overlapping regex matches in left-to-right
    scan order (re.finditer's natural order -- stable across Python versions/
    platforms). Each match is a candidate (operator_label, start, end,
    original_fragment, replacement_fragment). The full candidate list
    (operators concatenated in MUTATIONS order, each operator's matches in
    scan order) is then indexed with `random.Random(seed).randrange(len(...))`
    to pick exactly one candidate deterministically. Only that one match is
    replaced; every other occurrence of every operator is left untouched, so
    exactly one token in the module changes.

    Returns (corrupted_text, mutation_record) where mutation_record is a dict
    with keys: mutation (operator label from MUTATIONS), offset (character
    offset of the mutated fragment in spec_text), original (the matched
    fragment text), replacement (the fragment it was replaced with).

    If spec_text has NO site where any MUTATIONS regex matches at all, this
    raises NoCandidateMutation (documented choice: an exception, not a
    None-return, so a missed check isn't silently swallowed by a caller doing
    `if corrupted: ...`).
    """
    candidates = []
    for label, regex, replacement in MUTATIONS:
        for m in regex.finditer(spec_text):
            candidates.append((label, m.start(), m.end(), m.group(0), replacement))
    if not candidates:
        raise NoCandidateMutation(
            "no MUTATIONS operator site found in spec_text; nothing to corrupt")
    idx = random.Random(seed).randrange(len(candidates))
    label, start, end, original, replacement = candidates[idx]
    corrupted_text = spec_text[:start] + replacement + spec_text[end:]
    mutation_record = {
        "mutation": label,
        "offset": start,
        "original": original,
        "replacement": replacement,
    }
    return corrupted_text, mutation_record


# ------------------------------------------------------------- the prompts

_DESC_FIELD_ORDER = [
    "system_overview", "actors_and_components", "state_variables",
    "initial_state", "actions", "safety_properties", "liveness_properties",
    "model_bounds",
]

_DESC_FIELD_LABELS = {
    "system_overview": "System overview",
    "actors_and_components": "Actors and components",
    "state_variables": "State variables",
    "initial_state": "Initial state",
    "actions": "Actions",
    "safety_properties": "Safety properties",
    "liveness_properties": "Liveness properties",
    "model_bounds": "Model bounds",
}


def _format_description(description_json):
    """Render a FormaLLM description JSON as labeled sections, in a stable
    field order, skipping any fields absent from this particular description."""
    parts = []
    for key in _DESC_FIELD_ORDER:
        if key in description_json and description_json[key]:
            label = _DESC_FIELD_LABELS[key]
            parts.append(f"{label}: {description_json[key]}")
    # any extra fields not in the known order still get surfaced, sorted for determinism
    for key in sorted(description_json):
        if key not in _DESC_FIELD_ORDER and description_json[key]:
            parts.append(f"{key}: {description_json[key]}")
    return "\n\n".join(parts)


def _format_signature(sig):
    lines = []
    if sig["constants"]:
        lines.append("  CONSTANTS: " + ", ".join(sig["constants"]))
    if sig["specification"]:
        lines.append("  SPECIFICATION formula: " + sig["specification"])
    if sig["init"]:
        lines.append("  INIT predicate: " + sig["init"])
    if sig["next"]:
        lines.append("  NEXT action: " + sig["next"])
    if sig["invariants"]:
        lines.append("  INVARIANTS: " + ", ".join(sig["invariants"]))
    if sig["properties"]:
        lines.append("  PROPERTIES: " + ", ".join(sig["properties"]))
    return "\n".join(lines) if lines else "  (no identifiers required by the .cfg)"


GENERATION_PROMPT_TEMPLATE = """You are writing a TLA+ specification from a natural-language \
description of the system it must model. Below is the description, followed by the \
exact identifiers your module MUST define (derived from the reference TLC \
configuration that will be used to check it).

=== DESCRIPTION ===
{description}

=== REQUIRED IDENTIFIERS (from the reference .cfg) ===
{signature}

=== TASK ===
Write exactly ONE complete TLA+ module named {module_name} that defines every \
identifier listed above (the CONSTANTS as declared constants; the SPECIFICATION, \
INIT, NEXT, INVARIANTS, and PROPERTIES as operators with those exact names) and \
faithfully models the system described. Do not omit any required identifier and do \
not rename it.

Output ONLY the module, nothing else -- no prose before or after -- starting with \
`---- MODULE {module_name} ----` and ending with `====`."""


def build_generation_prompt(description_json, cfg_text, module_name):
    """Framing A prompt: FormaLLM description + required identifier signature
    (from required_signature(cfg_text)) -> instructions to emit exactly one
    TLA+ module named module_name, wrapped so extract_module can recover it."""
    return GENERATION_PROMPT_TEMPLATE.format(
        description=_format_description(description_json),
        signature=_format_signature(required_signature(cfg_text)),
        module_name=module_name)


REPAIR_PROMPT_TEMPLATE = """You are repairing a TLA+ specification so that it passes \
SANY (parser/semantic checker) and TLC model checking. Keep the change minimal and \
semantics-preserving with respect to the system being modeled; do NOT weaken or \
delete invariants/properties to force a pass.

=== SPEC ===
===BEGIN SPEC===
{broken_module}
===END SPEC===

=== FAILURE ===
{error_evidence}

Output the ENTIRE corrected module, nothing else, starting with `---- MODULE` and \
ending with `====`."""


def build_repair_prompt(broken_module, error_evidence):
    """Framing B prompt: mirrors the Stage-1 repair prompt shape in repair.py
    (spec text wrapped in BEGIN/END SPEC markers + error evidence), trimmed to
    the two pieces of text this framing has available (no fault-localized
    fragment or fixed .cfg criterion here -- those are runner/repair.py
    concerns for the full escalation loop, not this bare prompt builder)."""
    return REPAIR_PROMPT_TEMPLATE.format(
        broken_module=broken_module, error_evidence=error_evidence)


def summarize_passk(results, k):
    """results: {spec -> {"greedy": bool, "samples": [bool,...]}}.
    pass@1 counts specs whose temp-0 greedy sample passed; pass@k counts specs
    where any of the k drawn samples passed. Both spec lists are returned sorted
    numerically for a stable ledger."""
    p1 = sorted((s for s, r in results.items() if r.get("greedy")), key=int)
    pk = sorted((s for s, r in results.items() if any(r.get("samples", []))),
                key=int)
    return {"n": len(results), "pass@1": len(p1), f"pass@{k}": len(pk),
            "pass@1_specs": p1, f"pass@{k}_specs": pk}


# --------------------------------------------------------- orchestration

def holdout_specs_and_hash():
    """The frozen 30-spec holdout (corpus/holdout_30.json, DO NOT MODIFY) and the
    sha256 of that file's bytes at read time -- this IS the "frozen holdout hash"
    the E2.c handoff refers to (PLAN ledger entry 11 records the same digest,
    ecfc2053...54f78, computed the identical way -- sha256 of the whole file).
    Framing-B corruption seeds are derived from this hash + spec number so they
    are reproducible from the repo alone, with zero extra state to keep in sync."""
    raw = HOLDOUT_FILE.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    specs = [str(n) for n in json.loads(raw)["holdout_specs"]]
    return specs, digest


def corruption_seed(holdout_hash: str, num: str):
    """Deterministic per-spec Framing-B corruption seed: int(sha256(f"{holdout_hash}:
    {num}").hexdigest()[:8], 16). Documented derivation (E2.c handoff): a function
    of the frozen holdout hash and the spec number only, so it is reproducible from
    the repo alone and cannot be influenced by anything downstream of freezing."""
    h = hashlib.sha256(f"{holdout_hash}:{num}".encode()).hexdigest()
    return int(h[:8], 16)


def canonical_spec_text(num: str, corpus: Path):
    """Same source precedence as runner/repair: a committed patch overrides the
    corpus original. Reads tla_files/{num}.tla DIRECTLY by spec number -- never
    via mod2path, which is keyed by module name and so drops duplicate corpus
    entries (spec 158 is byte-identical to 164 [module Voting], 183 to 86
    [module TLAPS]; build_module_index keeps only the last path per module
    name, so a mod2path scan finds no path with stem 158/183)."""
    patch = REPO / "corpus" / "configs" / "patches" / f"{num}.tla"
    if patch.exists():
        return patch.read_text(errors="replace")
    src = corpus / "tla_files" / f"{num}.tla"
    if not src.exists():
        raise FileNotFoundError(f"no tla_files/{num}.tla in corpus")
    return src.read_text(errors="replace")


def row_key(row):
    return (row["spec"], row["sample"])


def load_existing_rows(rows_path: Path):
    """(spec, sample) pairs already present in a prior rows.jsonl, for --resume."""
    done = set()
    if rows_path.exists():
        for line in rows_path.read_text().splitlines():
            if line:
                r = json.loads(line)
                done.add((r["spec"], r["sample"]))
    return done


def _error_evidence(verdict_row, log_text):
    """Compact failure evidence for the Framing-B repair prompt: prefer the raw
    SANY/TLC log tail eval_module_text already wrote (same evidence a human or
    the Stage-1 repair loop would see), falling back to the row's own fields."""
    if log_text:
        return log_text if len(log_text) <= 8000 else \
            log_text[:2000] + "\n...[truncated]...\n" + log_text[-6000:]
    return (f"sany={verdict_row.get('sany')} tlc={verdict_row.get('tlc')} "
            f"tlc_vacuity={verdict_row.get('tlc_vacuity')} tlaps={verdict_row.get('tlaps')}")


def _score(num, module_text, corpus, num2mod, mod2path, cfg_dirs, workroot, logdir,
          timeout, log_name=None):
    row = eval_module_text(num, module_text, corpus, num2mod, mod2path, cfg_dirs,
                           workroot, logdir, timeout, stages=("sany", "tlc", "tlaps"),
                           log_name=log_name)
    # eval_module_text always sets row["sany"] (a headerless candidate gets
    # sany="no_module_header"), so verdict_of covers every outcome.
    verdict = verdict_of(num, row)
    log_path = Path(row["log_path"])
    log_text = log_path.read_text(errors="replace") if log_path.exists() else ""
    return row, verdict, log_text


def _persist_candidate(candidates_dir, spec, framing, sample_id, module_text, reply):
    """Rule 9 audit prerequisite (E2.c framing-B semantic diff audit): persist
    exactly what got scored so every sample is later inspectable.

    On successful extraction, writes module_text (the extract_module output --
    the SAME text passed to eval_module_text/_score) to
    candidates/{spec}-{framing}-{sample}.tla. When extraction failed
    (module_text is None), writes the raw model reply instead to
    candidates/{spec}-{framing}-{sample}.response.txt so failures are
    auditable too, and no sha256/candidate_path fields are produced (nothing
    was scored).

    Returns (candidate_path, candidate_sha256) -- both relative to the run
    directory (candidates_dir's parent) as POSIX strings, or (candidate_path,
    None) for the failure/.response.txt case.
    """
    candidates_dir.mkdir(parents=True, exist_ok=True)
    rundir = candidates_dir.parent
    if module_text is None:
        path = candidates_dir / f"{spec}-{framing}-{sample_id}.response.txt"
        path.write_text(reply if isinstance(reply, str) else str(reply))
        return path.relative_to(rundir).as_posix(), None
    path = candidates_dir / f"{spec}-{framing}-{sample_id}.tla"
    path.write_text(module_text)
    sha = hashlib.sha256(module_text.encode()).hexdigest()
    return path.relative_to(rundir).as_posix(), sha


def find_valid_corruption(spec_text, seed, scorer):
    """E2C_HANDOFF §4 step 3 precondition: the corrupted module must still
    SANY-parse AND fail the population criterion -- otherwise the repair task is
    either unparseable noise (repairing a syntax error is a different, easier
    task than repairing a semantic bug) or vacuous (nothing to repair).

    Deterministic site fallback: enumerate ALL candidate mutation sites in the
    same stable order corrupt() uses (MUTATIONS operator order, then re.finditer
    scan order), start at the seeded index (identical to corrupt()'s pick, so
    when the seeded candidate is valid the two functions agree exactly), and
    walk the ring. Each candidate's corrupted text is scored by `scorer(text) ->
    (row, verdict, log_text)` (real SANY + criterion via eval_module_text in
    production; stubbed in unit tests). Accept the first candidate with
    row["sany"] == "pass" and verdict != "pass".

    Returns (corrupted_text, mutation_record, error_evidence) on success --
    mutation_record additionally carries candidate_index, seeded_index,
    candidates_total, rejected (each rejected candidate's index/mutation/reason/
    verdict) and corrupted_verdict. On failure returns (None, skip_record, None)
    where skip_record["skip"] is "no_mutation_site" (zero candidates) or
    "no_valid_corruption" (every candidate rejected, rejections listed)."""
    candidates = []
    for label, regex, replacement in MUTATIONS:
        for m in regex.finditer(spec_text):
            candidates.append((label, m.start(), m.end(), m.group(0), replacement))
    if not candidates:
        return None, {"skip": "no_mutation_site", "candidates_total": 0}, None
    start = random.Random(seed).randrange(len(candidates))
    rejected = []
    for j in range(len(candidates)):
        idx = (start + j) % len(candidates)
        label, s, e, original, replacement = candidates[idx]
        text = spec_text[:s] + replacement + spec_text[e:]
        row, verdict, log_text = scorer(text)
        if row.get("sany") == "pass" and verdict != "pass":
            record = {"mutation": label, "offset": s, "original": original,
                      "replacement": replacement, "candidate_index": idx,
                      "seeded_index": start, "candidates_total": len(candidates),
                      "rejected": rejected, "corrupted_verdict": verdict}
            return text, record, log_text
        rejected.append({"candidate_index": idx, "mutation": label,
                         "reason": ("sany_fail" if row.get("sany") != "pass"
                                    else "still_passes"),
                         "verdict": verdict})
    return None, {"skip": "no_valid_corruption", "seeded_index": start,
                  "candidates_total": len(candidates), "rejected": rejected}, None


def gen_eval_spec_framing_a(num, description_json, cfg_text, module_name_for_spec,
                            model, run_id, k, corpus, num2mod, mod2path, cfg_dirs,
                            workroot, logdir, done, candidates_dir=None):
    """Framing A: one greedy (temperature 0) + k temperature-0.8 samples, each
    generated independently from the same generation prompt, extracted and scored.
    Yields row dicts (does not write them -- caller owns the JSONL/resume ledger).

    candidates_dir, if given, persists every candidate (or, on extraction
    failure, the raw reply) via _persist_candidate, and the returned row
    carries candidate_path/candidate_sha256 (see _persist_candidate)."""
    prompt = build_generation_prompt(description_json, cfg_text, module_name_for_spec)
    prompt_sha = hashlib.sha256(prompt.encode()).hexdigest()
    samples = [("greedy", 0.0)] + [(i, TEMPERATURE) for i in range(1, k + 1)]
    replies = _prefetch_replies(model, prompt, samples, done, num)
    for sample_id, temperature in samples:
        if (num, sample_id) in done:
            continue
        reply, model_s = replies[sample_id]
        module_text = extract_module(reply)
        base = {"spec": num, "framing": "A", "model": model.id,
                "prompt_sha256": prompt_sha, "sample": sample_id,
                "temperature": temperature, "timestamp": time.time()}
        if candidates_dir is not None:
            cand_path, cand_sha = _persist_candidate(
                candidates_dir, num, "A", sample_id, module_text, reply)
            if module_text is not None:
                base["candidate_path"] = cand_path
                base["candidate_sha256"] = cand_sha
        if module_text is None:
            err = isinstance(reply, str) and reply.startswith("[api_error")
            yield {**base, "verdict": "api_error" if err else "no_module_extracted",
                  "budget_used": {"model_s": model_s}}
            continue
        log_name = f"{num}-A-{sample_id}.log"
        row, verdict, _ = _score(num, module_text, corpus, num2mod, mod2path,
                                 cfg_dirs, workroot, logdir, TLC_TIMEOUT_S,
                                 log_name=log_name)
        row["budget_used"]["model_s"] = model_s
        yield {**base, "verdict": verdict, **{k2: v for k2, v in row.items()
                                              if k2 not in ("spec",)}}


def gen_eval_spec_framing_b(num, corrupted_text, mutation_record, seed,
                            error_evidence, model, run_id, k, corpus, num2mod,
                            mod2path, cfg_dirs, workroot, logdir, done,
                            candidates_dir=None):
    """Framing B repair sampling: given a PRECOMPUTED valid corruption (from
    find_valid_corruption -- corrupted text SANY-parses, criterion fails) and
    its error evidence, build the repair prompt, then one greedy + k
    temperature-0.8 samples of repair attempts. Yields row dicts (with
    mutation_record on every row, per the E2.c handoff).

    candidates_dir, if given, persists every candidate (or, on extraction
    failure, the raw reply) via _persist_candidate, and the returned row
    carries candidate_path/candidate_sha256 (see _persist_candidate)."""
    error_evidence = _error_evidence({}, error_evidence)
    prompt = build_repair_prompt(corrupted_text, error_evidence)
    prompt_sha = hashlib.sha256(prompt.encode()).hexdigest()
    samples = [("greedy", 0.0)] + [(i, TEMPERATURE) for i in range(1, k + 1)]
    replies = _prefetch_replies(model, prompt, samples, done, num)
    for sample_id, temperature in samples:
        if (num, sample_id) in done:
            continue
        reply, model_s = replies[sample_id]
        module_text = extract_module(reply)
        base = {"spec": num, "framing": "B", "model": model.id,
                "prompt_sha256": prompt_sha, "sample": sample_id,
                "temperature": temperature, "timestamp": time.time(),
                "mutation_record": mutation_record, "seed": seed}
        if candidates_dir is not None:
            cand_path, cand_sha = _persist_candidate(
                candidates_dir, num, "B", sample_id, module_text, reply)
            if module_text is not None:
                base["candidate_path"] = cand_path
                base["candidate_sha256"] = cand_sha
        if module_text is None:
            err = isinstance(reply, str) and reply.startswith("[api_error")
            yield {**base, "verdict": "api_error" if err else "no_module_extracted",
                  "budget_used": {"model_s": model_s}}
            continue
        log_name = f"{num}-B-{sample_id}.log"
        row, verdict, _ = _score(num, module_text, corpus, num2mod, mod2path,
                                 cfg_dirs, workroot, logdir, TLC_TIMEOUT_S,
                                 log_name=log_name)
        row["budget_used"]["model_s"] = model_s
        yield {**base, "verdict": verdict, **{k2: v for k2, v in row.items()
                                              if k2 not in ("spec",)}}


def run_gen_eval(corpus: Path, run_id: str, framing: str, model_name: str, k: int,
                 specs=None, resume=True):
    """CLI entry point (harness gen-eval). Runs Framing A or B over the (possibly
    --specs-restricted) frozen holdout, strictly sequentially (one spec/sample's
    TLC at a time -- Rule: no thread pool here, same contention discipline as
    repair.py), appending rows to results/runs/{run_id}/rows.jsonl (Rule 8:
    append-only; resume by skipping (spec, sample) pairs already present).
    Writes config.json up front and summary.json/.csv at the end."""
    all_specs, holdout_hash = holdout_specs_and_hash()
    todo = [s for s in all_specs if not specs or s in specs]
    if not todo:
        raise SystemExit("no specs selected (check --specs against holdout_30.json)")

    rundir = REPO / "results" / "runs" / run_id
    logdir = rundir / "logs"
    logdir.mkdir(parents=True, exist_ok=True)
    candidates_dir = rundir / "candidates"
    candidates_dir.mkdir(parents=True, exist_ok=True)
    workroot = Path("/tmp/prove-tla-gen-eval") / run_id
    model = make_model(model_name) if model_name != "local-stub" else _LocalStubModel()

    num2mod, mod2path = build_module_index(corpus)
    cfg_dirs = [("override", REPO / "corpus" / "configs" / "overrides"),
                ("original", corpus / "cfg"),
                ("draft", REPO / "corpus" / "configs" / "drafts")]

    rows_path = rundir / "rows.jsonl"
    done = load_existing_rows(rows_path) if resume else set()

    config = {
        "run_id": run_id, "framing": framing, "model": model.id,
        "corpus": str(corpus), "k": k,
        "holdout_sha256": holdout_hash, "holdout_specs": all_specs,
        "n_specs": len(todo),
        "budget": {"temperature": TEMPERATURE, "max_tokens": MAX_TOKENS,
                   "tlc_timeout_s": TLC_TIMEOUT_S, "k": k, "pass1": "greedy@temp0",
                   "sequential": True},
        "command": (f"python3 -m harness gen-eval --framing {framing} "
                   f"--model {model_name} --run-id {run_id} --k {k}"),
    }
    (rundir / "config.json").write_text(json.dumps(config, indent=2))

    results = {}  # spec -> {"greedy": bool, "samples": [bool,...]}
    with open(rows_path, "a") as fh:
        for i, num in enumerate(todo, 1):
            if framing == "A":
                desc = json.loads((corpus / "descriptions" / f"{num}.json").read_text())
                cfg_text, _ = _resolve_cfg(num, cfg_dirs)
                mod = num2mod.get(num)
                if mod is None or cfg_text is None:
                    print(f"[{i}/{len(todo)}] spec {num}: skipped (no module/cfg)")
                    continue
                gen = gen_eval_spec_framing_a(
                    num, desc, cfg_text, mod, model, run_id, k, corpus, num2mod,
                    mod2path, cfg_dirs, workroot, logdir, done,
                    candidates_dir=candidates_dir)
            else:
                def skip_row(verdict, extra=None):
                    """Skips are LEDGERED rows (Rule 8), never console-only."""
                    row = {"spec": num, "framing": "B", "model": model.id,
                           "sample": "corruption", "verdict": verdict,
                           "timestamp": time.time(), **(extra or {})}
                    if (num, "corruption") not in done:
                        fh.write(json.dumps(row) + "\n")
                        fh.flush()
                try:
                    canonical = canonical_spec_text(num, corpus)
                except FileNotFoundError:
                    skip_row("skipped:no_source_file")
                    print(f"[{i}/{len(todo)}] spec {num}: skipped (no source file)")
                    continue
                seed = corruption_seed(holdout_hash, num)
                corrupted, mutation_record, evidence = _corruption_for_spec(
                    num, canonical, seed, rundir, corpus, num2mod, mod2path,
                    cfg_dirs, workroot, logdir)
                if corrupted is None:
                    skip_row(f"skipped:{mutation_record['skip']}",
                            {"mutation_record": mutation_record, "seed": seed})
                    print(f"[{i}/{len(todo)}] spec {num}: "
                         f"skipped ({mutation_record['skip']}) [ledgered]")
                    continue
                gen = gen_eval_spec_framing_b(
                    num, corrupted, mutation_record, seed, evidence, model,
                    run_id, k, corpus, num2mod, mod2path, cfg_dirs, workroot,
                    logdir, done, candidates_dir=candidates_dir)
            r = results.setdefault(num, {"greedy": False, "samples": []})
            n_written = 0
            for row in gen:
                fh.write(json.dumps(row) + "\n")
                fh.flush()
                n_written += 1
                passed = row.get("verdict") == "pass"
                if row["sample"] == "greedy":
                    r["greedy"] = passed
                else:
                    r["samples"].append(passed)
            print(f"[{i}/{len(todo)}] spec {num}: {n_written} sample(s) run "
                 f"(resumed {sum(1 for s in done if s[0] == num)} skipped)")
    shutil.rmtree(workroot, ignore_errors=True)

    summary = summarize_passk(results, k)
    (rundir / "summary.json").write_text(json.dumps(summary, indent=2))
    with open(rundir / "summary.csv", "w") as fh:
        fh.write("spec,greedy_pass,any_sample_pass,n_samples\n")
        for num, r in sorted(results.items(), key=lambda kv: int(kv[0])):
            fh.write(f"{num},{r['greedy']},{any(r['samples'])},{len(r['samples'])}\n")
    print(f"\n=== {run_id}: framing {framing}, model={model.id} ===")
    print(f"  n={summary['n']}  pass@1={summary['pass@1']}  pass@{k}={summary[f'pass@{k}']}")
    return summary


def _corruption_for_spec(num, canonical, seed, rundir, corpus, num2mod, mod2path,
                         cfg_dirs, workroot, logdir):
    """find_valid_corruption with a per-run cache (rundir/corruptions/{num}.json):
    the precondition check costs real SANY/TLC time per candidate, so a resumed
    run must not redo it. The cache stores the seed it was computed under; a
    mismatched seed (shouldn't happen -- seeds are pure functions of the frozen
    holdout hash) invalidates the entry rather than silently reusing it."""
    cachedir = rundir / "corruptions"
    cachedir.mkdir(exist_ok=True)
    cache = cachedir / f"{num}.json"
    if cache.exists():
        c = json.loads(cache.read_text())
        if c.get("seed") == seed:
            return c["corrupted_text"], c["mutation_record"], c["error_evidence"]

    def scorer(text):
        return _score(num, text, corpus, num2mod, mod2path, cfg_dirs, workroot,
                      logdir, TLC_TIMEOUT_S)

    corrupted, record, evidence = find_valid_corruption(canonical, seed, scorer)
    cache.write_text(json.dumps({
        "seed": seed, "corrupted_text": corrupted, "mutation_record": record,
        "error_evidence": evidence}, indent=2))
    return corrupted, record, evidence


def _resolve_cfg(num, cfg_dirs):
    for label, d in cfg_dirs:
        c = d / f"{num}.cfg"
        if c.exists():
            return c.read_text(errors="replace"), label
    return None, None


class _LocalStubModel:
    """Zero-spend dry-run model for --model local-stub: deterministic, ignores
    the prompt content and returns a fixed reply per framing shape so the whole
    pipeline (prompt build -> generate -> extract -> score -> ledger) runs without
    any network call. Framing A's reply never satisfies a real .cfg (LocalStub
    has no way to know the required identifiers), so expect fails there; Framing
    B's reply echoes the SPEC embedded in the prompt (the corrupted module)
    unchanged -- same behavior as harness.repair.LocalStub, reused here directly
    via the ===BEGIN SPEC=== marker gen_eval's own prompts also use."""
    id = "local-stub-v1"

    def generate(self, prompt, n, temperature, max_tokens):
        m = re.search(r"===BEGIN SPEC===\n(.*?)\n===END SPEC===", prompt, re.S)
        if m:
            return [m.group(1)] * n
        return ["---- MODULE Empty ----\n===="] * n
