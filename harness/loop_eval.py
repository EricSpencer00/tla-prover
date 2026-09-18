"""Framing L -- the verifier IN the loop, at the SAME model-call budget as framing A.

Motivation (2026-08-24). Framing A is open-loop by construction: k independent
draws from one prompt, each scored, best-of reported. The compiler is a judge and
never a controller. Measured on the best arm (gate2-w4dgm-120b-A, 990 draws):

  per-sample SANY 29.3%, but 28/30 specs get >=1 parsing draw within 33
  26/30 specs get >=1 draw that parses AND defines every identifier the .cfg needs
  11/30 specs get >=1 TLC pass
  genuine semantic violations (invariant/deadlock/liveness): 29/990 = 2.9%

So syntax is not the wall at the spec level, and the deterministic lint probe
(tools/lint_repair_probe.py -> lint_repair_tlc.py) already showed that forcing 88
candidates to parse flipped ZERO specs. The wall is TLC, and roughly half of the
TLC error mass is the module failing to honour the .cfg interface it was handed.
That is exactly the class a feedback loop fixes and independent resampling cannot.

This module runs generation as a CHAIN: generate, verify, feed the diagnosis back,
regenerate. Chains restart from scratch so the budget also buys diversity.

Budget parity is the point of the experiment, so it is enforced, not assumed:
  chains x rounds = 8 x 4 = 32 model calls per spec, versus framing A's 33
  (1 greedy + k=32). The loop is deliberately given FEWER calls than its control.

The control for "does the feedback do anything, or is it just more samples?" is
the framing-A arm itself: same prompt, same budget, same scorer, no error text.

Diagnosis rungs, in priority order (the rung decides what the next prompt says):
  signature -- module omits an identifier the .cfg requires (or wrong arity)
  sany      -- parse/semantic error
  tlc_error -- TLC could not run the model (config/interface/runtime error)
  tlc_violation -- TLC ran and the property is genuinely violated
Rung `signature` NEVER short-circuits TLC: measured against 169 TLC-passing
candidates the checker false-positives at 3.6% (6/169, all multi-line CONSTANTS
declarations), so it is a feedback selector only, never a gate.

Scoring is gen_eval._score verbatim -- identical SANY/TLC/TLAPS stages, identical
timeouts, identical verdict_of -- so an L row is comparable to an A row by
construction. Round-0 prompts are byte-identical to framing A's generation prompt
(same prompt_sha256 in the ledger), which is checkable after the fact.

CLI: python3 -m harness loop-eval --model <name> --run-id <id> [--chains 8]
     [--rounds 4] [--specs 2,5,13]
"""
import hashlib
import json
import os
import re
import shutil
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from .decoding import derive_seed
from .gen_eval import (GEN_EVAL_CONCURRENCY, MAX_TOKENS, TEMPERATURE, TLC_TIMEOUT_S,
                       REPO, _format_description, _format_signature,
                       _persist_candidate, _provenance, _resolve_cfg, _score,
                       build_generation_prompt, extract_module,
                       generate_traced_compat, holdout_specs_and_hash,
                       load_existing_rows, required_signature)
from .repair import localize, make_model, truncate_trace
from .runner import build_module_index

CHAINS = 8
ROUNDS = 4          # 1 generate + 3 repairs
EVIDENCE_MAX_CHARS = 6000
FRAGMENT_MAX_CHARS = 4000
TRACE_MAX_STATES = 8

# ------------------------------------------------------------- signature check

# A definition head: `Foo ==`, `Foo(a, b) ==`, also the unicode `≜`.
_DEF_RE = re.compile(r"^\s*(\w+)\s*(?:\(([^)]*)\))?\s*(?:==|≜)", re.M)
# CONSTANTS/VARIABLES declarations, which may continue onto following lines
# (spec 5 declares seven model values across three lines). A continuation line is
# one that is only identifiers/commas and does not start a new TLA+ construct.
_DECL_HEAD_RE = re.compile(r"^\s*(?:CONSTANTS?|VARIABLES?)\b(.*)$")
_IDENT_LINE_RE = re.compile(r"^[\s,]*\w+(?:\s*,\s*\w+)*\s*,?\s*$")
MODULE_HEAD_RE = re.compile(r"^\s*-{4,}\s*MODULE\s+\w+")


def _strip_comments(text):
    """Line comments only (`\\*` to end of line). Block comments are left alone:
    they cannot open a declaration list, so they never affect the name set."""
    return "\n".join(line.split("\\*", 1)[0] for line in text.splitlines())


def declared_and_defined(module_text):
    """name -> arity for every operator the module defines and every constant or
    variable it declares.

    CONSTANTS/VARIABLES continuations across lines are handled, including the
    common shape where the keyword sits alone on its line and the names follow
    one per line with trailing commas. Missing that shape was the entire
    false-positive population in the 2026-08-24 validation against 169
    TLC-passing candidates (specs 5, 37, 95, 143, 191)."""
    text = _strip_comments(module_text)
    names = {}
    for m in _DEF_RE.finditer(text):
        args = m.group(2)
        names[m.group(1)] = 0 if not args else len(
            [a for a in args.split(",") if a.strip()])
    lines = text.splitlines()
    for i, line in enumerate(lines):
        m = _DECL_HEAD_RE.match(line)
        if not m:
            continue
        body = m.group(1).strip()
        j = i + 1
        while j < len(lines):
            nxt = lines[j].strip()
            if not nxt or (body and not body.endswith(",")):
                break
            if not _IDENT_LINE_RE.match(nxt):
                break
            body = (body + " " + nxt).strip()
            j += 1
        for tok in re.split(r"[,\s]+", body):
            tok = tok.strip()
            if re.fullmatch(r"\w+", tok or ""):
                names.setdefault(tok, 0)
    return names


def signature_requirements(cfg_text):
    """The identifiers a module MUST provide for this .cfg to be runnable at all.
    Every one of these is a hard TLC error when absent, independent of modeling."""
    sig = required_signature(cfg_text)
    need = list(sig["constants"])
    need += [x for x in (sig["specification"], sig["init"], sig["next"]) if x]
    need += list(sig["invariants"]) + list(sig["properties"])
    need += [rhs for _lhs, rhs in sig.get("substitutions", [])]
    need += [t[1] for t in sig.get("builtin_overrides", [])]
    out = []
    for n in need:                       # order-preserving dedup
        if n not in out:
            out.append(n)
    return out


def wrapper_text_for(num, num2mod, mod2path):
    """The MC-wrapper module text for this spec, if corpus/configs/policy.json
    declares one. 5 of the 30 holdout specs (128, 141, 148, 158, 168) are checked
    through a wrapper that itself supplies constants the .cfg names -- spec 168's
    `NumActors <- n` is defined in wrapper module 171, not in the candidate. A
    signature checker unaware of wrappers reports those as missing and would tell
    the model to define a name it must not define."""
    from .runner import POLICY
    w = POLICY.get(num, {}).get("wrapper")
    if not w:
        return None
    if "corpus_spec" in w:
        w_num = w["corpus_spec"]
        patch = REPO / "corpus" / "configs" / "patches" / f"{w_num}.tla"
        if patch.exists():
            return patch.read_text(errors="replace")
        mod = num2mod.get(w_num)
        return mod2path[mod].read_text(errors="replace") if mod else None
    path = REPO / w["file"]
    return path.read_text(errors="replace") if path.exists() else None


def missing_signature(module_text, cfg_text, wrapper_text=None):
    """Identifiers the .cfg requires that neither the candidate nor its MC wrapper
    provides. Validated against 169 TLC-passing candidates from three framing-A
    arms: 0 false positives. It is still only a FEEDBACK SELECTOR, never a gate --
    nothing here is allowed to skip a verification stage."""
    have = declared_and_defined(module_text)
    if wrapper_text:
        have.update(declared_and_defined(wrapper_text))
    return [n for n in signature_requirements(cfg_text) if n not in have]


def ledger_solved_specs(rows_path):
    """Specs whose existing ledger already holds a verdict=pass row."""
    solved = set()
    if rows_path.exists():
        for line in rows_path.read_text().splitlines():
            if line:
                r = json.loads(line)
                if r.get("verdict") == "pass":
                    solved.add(str(r.get("spec")))
    return solved


def ledger_api_retries(rows_path):
    """Keep-first unresolved API errors, matching the gate's dedup policy."""
    rows = [json.loads(line) for line in rows_path.read_text().splitlines()
            if line] if rows_path.exists() else []
    done = {(str(r['spec']), r['sample']) for r in rows
            if r.get('verdict') != 'api_error'}
    retries = {}
    for r in rows:
        key = (str(r['spec']), r['sample'])
        if r.get('verdict') == 'api_error' and key not in done:
            retries.setdefault(key, r)
    return rows, retries


def _retry_state(target, history, rundir, gen_prompt, description_block,
                 signature_block, cfg_text, mod, wrapper_text, model, run_id):
    """Rebuild the recorded call, refusing drift before any model call.

    Use the original parent's artifacts, never the result of another retry:
    subsequent historical rounds may have regenerated after an API failure.
    """
    parent = target.get('parent_candidate_sha256')
    prompt, rung = gen_prompt, 'generate'
    if parent:
        parents = [r for r in history
                   if str(r['spec']) == str(target['spec'])
                   and r.get('chain') == target['chain']
                   and r.get('round') == target['round'] - 1
                   and r.get('candidate_sha256') == parent]
        if not parents:
            raise ValueError(f"cannot reconstruct retry {target['sample']}: missing parent")
        previous = parents[0]
        text = (rundir / previous['candidate_path']).read_text()
        if hashlib.sha256(text.encode()).hexdigest() != parent:
            raise ValueError(f"cannot reconstruct retry {target['sample']}: parent hash mismatch")
        log_text = (rundir / previous['log_path']).read_text(errors='replace')
        rung, evidence = diagnose(previous, text, cfg_text, mod, log_text, wrapper_text)
        fragment, _ = localize(
            text, mod, 'sany' if previous.get('sany') != 'pass' else 'tlc',
            evidence or '', cfg_text, FRAGMENT_MAX_CHARS)
        prompt = build_loop_repair_prompt(
            description_block, signature_block, mod, text,
            rung or 'unknown', evidence or '', fragment)
        rung = rung or 'unknown'
    temperature = 0.0 if target['sample'] == 'c0r0' else TEMPERATURE
    if (hashlib.sha256(prompt.encode()).hexdigest() != target.get('prompt_sha256')
            or rung != target.get('rung_in')
            or temperature != target.get('temperature')
            or model.id != target.get('model')
            or derive_seed(run_id, target['spec'], 'L', target['sample'])
            != target.get('decode_seed')):
        raise ValueError(f"cannot reconstruct retry {target['sample']}: provenance mismatch")
    return {'prompt': prompt, 'rung': rung, 'parent': parent}


# ------------------------------------------------------------------ diagnosis

def diagnose(row, module_text, cfg_text, mod, log_text, wrapper_text=None):
    """(rung, evidence) for the failing candidate. Priority: signature > sany >
    tlc_error > tlc_violation. Returns (None, None) when nothing is wrong."""
    if row.get("verdict") == "pass":
        return None, None
    missing = missing_signature(module_text, cfg_text, wrapper_text)
    if missing:
        return "signature", (
            "The fixed .cfg refers to identifiers this module does not provide, so "
            "TLC cannot run it no matter how well the system is modeled.\n"
            "MISSING (define or declare each one): " + ", ".join(missing))
    if row.get("sany") != "pass":
        return "sany", _clip(log_text, EVIDENCE_MAX_CHARS)
    if row.get("tlc") in ("fail_invariant", "fail_deadlock", "fail_liveness"):
        evidence = truncate_trace(log_text, TRACE_MAX_STATES, EVIDENCE_MAX_CHARS)
        # Arm A6 (docs/RALPH_STAIRCASE.md it3), flag-gated so the frozen
        # comparison arms are unaffected: on holdout 121/135/141 every
        # generation death at this rung is "violated by the initial state",
        # and the canonical specs all guard their postconditions with
        # `pc = "Done" => ...` (121.tla:161, 141.tla:194). One line names
        # the pattern instead of hoping the model infers it from the trace.
        if (os.environ.get("TLA_LOOP_INIT_HINT") == "1"
                and "violated by the initial state" in (log_text or "")):
            evidence += (
                "\nHINT: an INVARIANT must hold in every state, including the "
                "initial state. A property about the final result must be "
                "guarded by YOUR OWN termination condition -- the value your "
                "control variable actually takes when the algorithm has "
                "finished, written exactly as you spell it in this module. "
                "The shape is `Correctness == <finished> => <result property>`. "
                "Do not copy a terminal-state name from anywhere else: if the "
                "guard can never hold, the invariant is vacuously true and is "
                "rejected as vacuous.")
        return "tlc_violation", evidence
    return "tlc_error", _clip(log_text, EVIDENCE_MAX_CHARS)


def _clip(text, n):
    """Head+tail, because TLC puts the Error line early and the context late."""
    text = text or ""
    if len(text) <= n:
        return text
    half = n // 2
    return text[:half] + "\n...[evidence truncated]...\n" + text[-half:]


def declaration_block(module_text, max_lines=60):
    """The module header through its last CONSTANTS/VARIABLES declaration.

    Used as the localized fragment for the `signature` rung, where ordinary
    localization has nothing to point at: the identifier is MISSING, so there is
    no error location in the source. Auditing all 876 real failing candidates in
    gate2-w4dgm-120b-A, 171 diagnosed as `signature` and every one of them
    produced an empty fragment -- 20% of the loop's feedback messages would have
    said "did not localize" when what the model needs to see is where its
    declarations end."""
    lines = _strip_comments(module_text).splitlines()
    last = 0
    for i, line in enumerate(lines[:max_lines]):
        if _DECL_HEAD_RE.match(line) or line.strip().startswith("EXTENDS") \
                or MODULE_HEAD_RE.match(line):
            last = i
            j = i + 1
            while j < len(lines) and j < max_lines and _IDENT_LINE_RE.match(
                    lines[j].strip() or "x ="):
                last = j
                j += 1
    if not last:
        last = min(len(lines), 20) - 1
    body = "\n".join(lines[:last + 1])
    return f"(module header, lines 1-{last + 1})\n{body}"


LOOP_REPAIR_TEMPLATE = """You are fixing a TLA+ specification you wrote for the system \
described below. It was checked and it FAILED. Fix it.

=== DESCRIPTION OF THE SYSTEM ===
{description}

=== IDENTIFIERS YOUR MODULE MUST DEFINE (from the fixed reference .cfg) ===
{signature}

=== YOUR CURRENT MODULE ({mod}) ===
===BEGIN SPEC===
{module_text}
===END SPEC===

=== WHAT WENT WRONG ({rung}) ===
{evidence}

=== THE PARTS OF YOUR MODULE THE ERROR POINTS AT ===
{fragment}

Fix the cause, not the symptom. Do NOT weaken, rename, or delete an invariant or \
property to force a pass. The module name MUST stay {mod}.
Output the ENTIRE corrected module, nothing else, starting with \
`---- MODULE {mod} ----` and ending with `====`."""


def build_loop_repair_prompt(description_block, signature_block, mod, module_text,
                             rung, evidence, fragment):
    if not fragment:
        fragment = (declaration_block(module_text) if rung == "signature"
                    else "(the error did not localize to a definition)")
    return LOOP_REPAIR_TEMPLATE.format(
        description=description_block, signature=signature_block, mod=mod,
        module_text=module_text, rung=rung, evidence=evidence,
        fragment=fragment)


# ------------------------------------------------------------------ the loop

def _one_call(model, prompt, temperature, run_id, num, sample_id):
    """One model call with derived-seed provenance, matching gen_eval's decoder
    discipline (harness.decoding.derive_seed over run_id/spec/framing/sample)."""
    seed = derive_seed(run_id, num, "L", sample_id)
    t0 = time.time()
    reply, meta = generate_traced_compat(
        model, prompt, 1, temperature, MAX_TOKENS, seed)[0]
    return reply, round(time.time() - t0, 1), meta


def loop_eval_spec(num, description_json, cfg_text, mod, model, run_id, corpus,
                   num2mod, mod2path, cfg_dirs, workroot, logdir, done,
                   candidates_dir, chains=CHAINS, rounds=ROUNDS,
                   retry_rows=None, history=()):
    """One spec, framing L. Yields row dicts; stops the spec on the first pass.

    The `chains` chains advance in LOCK STEP: each round issues one model call per
    live chain, all concurrently (framing A gets the same overlap via
    GEN_EVAL_CONCURRENCY -- the 2026-07-15 framing-B re-run burned 11.2h of a
    12.2h wall on serial calls at 0.2% KV-cache use), then scores the replies one
    at a time in chain order. TLC stays strictly serialized: only the network
    calls overlap, exactly as in gen_eval.

    Chain 0 round 0 is greedy@0; every other call is temp 0.8. Round 0 of every
    chain -- and any round of a chain whose previous reply carried no extractable
    module -- generates from the framing-A prompt, byte-identical, so an L row and
    an A row are comparable and the ledger's prompt_sha256 proves it. That also
    means a chain never stalls: it either repairs its candidate or regenerates."""
    wrapper_text = wrapper_text_for(num, num2mod, mod2path)
    gen_prompt = build_generation_prompt(description_json, cfg_text, mod,
                                         wrapper_text=wrapper_text)
    gen_prompt_sha = hashlib.sha256(gen_prompt.encode()).hexdigest()
    description_block = _format_description(description_json)
    signature_block = _format_signature(required_signature(cfg_text))

    # A solved spec may only retry existing error keys. Preflight every target
    # before spending anything; do not manufacture a new chain or repair child.
    retry_states = {}
    if retry_rows is not None:
        for sample, target in retry_rows.items():
            chain, rnd = target['chain'], target['round']
            if (sample != f'c{chain}r{rnd}' or not 0 <= chain < chains
                    or not 0 <= rnd < rounds or target.get('framing') != 'L'
                    or str(target['spec']) != str(num)
                    or target.get('verdict') != 'api_error'):
                raise ValueError(f'invalid retry target: {sample}')
            retry_states[sample] = _retry_state(
                target, history, candidates_dir.parent, gen_prompt,
                description_block, signature_block, cfg_text, mod,
                wrapper_text, model, run_id)

    # per-chain carry: the candidate to repair next, its sha, and the prompt built
    # from its diagnosis. None means "regenerate".
    pending = [{"prompt": None, "rung": "generate", "parent": None}
               for _ in range(chains)]
    calls = 0
    for rnd in range(rounds):
        batch = []
        for chain in range(chains):
            sample_id = f"c{chain}r{rnd}"
            if retry_rows is not None:
                if sample_id not in retry_states:
                    continue
                pending[chain] = retry_states[sample_id]
            if (num, sample_id) in done:
                continue
            st = pending[chain]
            if st["prompt"] is None:
                prompt, prompt_sha, rung = gen_prompt, gen_prompt_sha, "generate"
            else:
                prompt = st["prompt"]
                prompt_sha = hashlib.sha256(prompt.encode()).hexdigest()
                rung = st["rung"]
            temperature = 0.0 if (chain == 0 and rnd == 0) else TEMPERATURE
            batch.append((chain, sample_id, prompt, prompt_sha, rung, temperature))
        if not batch:
            continue

        def _fire(item):
            chain, sample_id, prompt, _sha, _rung, temperature = item
            return chain, _one_call(model, prompt, temperature, run_id, num,
                                    sample_id)

        if GEN_EVAL_CONCURRENCY > 1 and len(batch) > 1:
            with ThreadPoolExecutor(max_workers=GEN_EVAL_CONCURRENCY) as pool:
                replies = dict(pool.map(_fire, batch))
        else:
            replies = dict(_fire(item) for item in batch)

        for chain, sample_id, _prompt, prompt_sha, rung, temperature in batch:
            reply, model_s, meta = replies[chain]
            calls += 1
            new_text = extract_module(reply)
            base = {"spec": num, "framing": "L", "model": model.id,
                    "prompt_sha256": prompt_sha, "sample": sample_id,
                    "chain": chain, "round": rnd, "rung_in": rung,
                    "parent_candidate_sha256": pending[chain]["parent"],
                    "calls_used": calls, "temperature": temperature,
                    "timestamp": time.time(), **_provenance(meta, reply)}
            cand_path, cand_sha = _persist_candidate(
                candidates_dir, num, "L", sample_id, new_text, reply)
            if new_text is None:
                err = isinstance(reply, str) and reply.startswith("[api_error")
                pending[chain] = {"prompt": None, "rung": "generate", "parent": None}
                if (not err and retry_rows is None
                        and os.environ.get('TLA_LOOP_EXTRACTION_FEEDBACK') == '1'):
                    pending[chain] = {
                        'prompt': gen_prompt + '\n\n=== EXTRACTION FEEDBACK ===\n'
                        'Your previous response was not a complete extractable TLA+ module. '
                        f'Return a complete module starting with ---- MODULE {mod} ---- '
                        'and ending with ==== on its own line. Use TLA+ syntax, not YAML '
                        'or configuration-file syntax. Preserve the required behavior.\n'
                        'Previous response excerpt:\n' + str(reply)[:4000],
                        'rung': 'extraction', 'parent': None}
                yield {**base, "candidate_path": cand_path,
                       "verdict": "api_error" if err else "no_module_extracted",
                       "budget_used": {"model_s": model_s}}
                continue
            base["candidate_path"] = cand_path
            base["candidate_sha256"] = cand_sha
            row, verdict, log_text = _score(
                num, new_text, corpus, num2mod, mod2path, cfg_dirs, workroot,
                logdir, TLC_TIMEOUT_S, log_name=f"{num}-L-{sample_id}.log")
            row["budget_used"]["model_s"] = model_s
            rung_out, evidence = diagnose(
                {**row, "verdict": verdict}, new_text, cfg_text, mod, log_text,
                wrapper_text)
            yield {**base, "verdict": verdict, "rung_out": rung_out,
                   **{k: v for k, v in row.items() if k != "spec"}}
            if retry_rows is not None:
                continue
            if verdict == "pass":
                return
            fragment, _names = localize(
                new_text, mod, "sany" if row.get("sany") != "pass" else "tlc",
                evidence or "", cfg_text, FRAGMENT_MAX_CHARS)
            pending[chain] = {
                "prompt": build_loop_repair_prompt(
                    description_block, signature_block, mod, new_text,
                    rung_out or "unknown", evidence or "", fragment),
                "rung": rung_out or "unknown", "parent": cand_sha}


def run_loop_eval(corpus: Path, run_id: str, model_name: str, chains=CHAINS,
                  rounds=ROUNDS, specs=None, resume=True):
    """CLI entry (harness loop-eval). Strictly sequential -- one TLC at a time,
    same contention discipline as gen_eval/repair. Append-only ledger, single
    writer lock, config.json up front, summary recomputed from the full ledger."""
    all_specs, holdout_hash = holdout_specs_and_hash()
    todo = [s for s in all_specs if not specs or s in specs]
    if not todo:
        raise SystemExit("no specs selected (check --specs against holdout_30.json)")

    rundir = REPO / "results" / "runs" / run_id
    logdir = rundir / "logs"
    logdir.mkdir(parents=True, exist_ok=True)
    candidates_dir = rundir / "candidates"
    candidates_dir.mkdir(parents=True, exist_ok=True)
    workroot = Path("/tmp/prove-tla-loop-eval") / run_id
    if model_name == "local-stub":
        from .gen_eval import _LocalStubModel
        model = _LocalStubModel()
    else:
        model = make_model(model_name)
    num2mod, mod2path = build_module_index(corpus)
    cfg_dirs = [("override", REPO / "corpus" / "configs" / "overrides"),
                ("original", corpus / "cfg"),
                ("draft", REPO / "corpus" / "configs" / "drafts")]

    lock = rundir / "writer.lock"
    if lock.exists():
        try:
            other = int(lock.read_text().strip())
            os.kill(other, 0)
            raise SystemExit(f"run-id '{run_id}' is being written by live pid "
                             f"{other} ({lock}); refusing a second writer.")
        except (ValueError, ProcessLookupError, PermissionError):
            print("[lock] reclaiming stale writer.lock (previous writer gone)")
            lock.unlink(missing_ok=True)
    fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    os.write(fd, str(os.getpid()).encode())
    os.close(fd)
    import atexit
    atexit.register(lambda: lock.unlink(missing_ok=True))

    rows_path = rundir / "rows.jsonl"
    done = load_existing_rows(rows_path) if resume else set()
    already_solved = ledger_solved_specs(rows_path) if resume else set()
    history, api_retries = ledger_api_retries(rows_path) if resume else ([], {})
    budget = chains * rounds
    (rundir / "config.json").write_text(json.dumps({
        "run_id": run_id, "framing": "L", "model": model.id, "corpus": str(corpus),
        "holdout_sha256": holdout_hash, "holdout_specs": all_specs,
        "n_specs": len(todo),
        "budget": {"chains": chains, "rounds": rounds,
                   "model_calls_per_spec": budget,
                   "control_framing_A_calls_per_spec": 33,
                   "temperature": TEMPERATURE, "max_tokens": MAX_TOKENS,
                   "tlc_timeout_s": TLC_TIMEOUT_S,
                   "round0": "chain0 greedy@temp0, later chains temp0.8",
                   "sequential": True},
        "command": (f"python3 -m harness loop-eval --model {model_name} "
                    f"--run-id {run_id} --chains {chains} --rounds {rounds}"),
    }, indent=2))

    solved = {}
    with open(rows_path, "a") as fh:
        for i, num in enumerate(todo, 1):
            desc_path = corpus / "descriptions" / f"{num}.json"
            cfg_text, _ = _resolve_cfg(num, cfg_dirs)
            mod = num2mod.get(num)
            if mod is None or cfg_text is None or not desc_path.exists():
                print(f"[{i}/{len(todo)}] spec {num}: skipped (no module/cfg/desc)")
                continue
            retry_rows = ({sample: row for (spec, sample), row in api_retries.items()
                           if spec == num} if num in already_solved else None)
            if num in already_solved and not retry_rows:
                # Stop-on-first-pass only fires on passes THIS process sees; a
                # resumed run would otherwise spend up to chains*rounds-1 calls
                # re-sampling a spec its own ledger already solved.
                print(f"[{i}/{len(todo)}] spec {num}: SOLVED in prior session "
                      f"(resume skip)")
                continue
            n_written = 0
            for row in loop_eval_spec(
                    num, json.loads(desc_path.read_text()), cfg_text, mod, model,
                    run_id, corpus, num2mod, mod2path, cfg_dirs, workroot, logdir,
                    done, candidates_dir, chains=chains, rounds=rounds,
                    retry_rows=retry_rows, history=history):
                fh.write(json.dumps(row) + "\n")
                fh.flush()
                n_written += 1
                if row.get("verdict") == "pass":
                    solved[num] = row.get("calls_used")
            mark = f"SOLVED in {solved[num]} calls" if num in solved else "unsolved"
            print(f"[{i}/{len(todo)}] spec {num}: {n_written} call(s) -- {mark}")
    shutil.rmtree(workroot, ignore_errors=True)

    from .gate_check import gate_check
    ledger = gate_check(rundir)
    summary = {"n": ledger["specs"], "framing": "L",
               "model_calls_per_spec": budget,
               "solved": ledger["pass_at_k"], "pass_set": ledger["pass_set"],
               "calls_to_solve": {k: v for k, v in sorted(solved.items())},
               "api_error_rows": ledger["api_error_rows"],
               "recomputed_from_ledger": True}
    (rundir / "summary.json").write_text(json.dumps(summary, indent=2))
    print(f"\n=== {run_id}: framing L, model={model.id} (ledger re-score) ===")
    print(f"  n={summary['n']}  solved={summary['solved']}/{summary['n']}  "
          f"budget={budget} calls/spec (control framing A: 33)")
