"""Stage-1 repair agent (PLAN.md W1.1).

Per-spec escalation schedule, FIXED in corpus/configs/repair_budget.json (never
inline), in this order:

  baseline        -- oracle-machinery evaluation of the spec as-is (failure evidence)
  repair-r1/r2    -- <=2 iterative rounds; each round's prompt carries the spec text,
                     the TLC counterexample *trace* or SANY/TLC error (truncated
                     head+tail), and a fault-localized fragment (TraceFix/MaxSAT
                     lesson: feed the model the definitions the trace actually
                     exercised, not the whole module again)
  repair-bestofN  -- N independent samples at higher temperature (pass@N reported
                     separately from pass@1 per Rule 3)
  repair-mutation -- SpecGen-style symbolic operator swaps (harness.mutation's
                     MUTATIONS) applied to near-misses: candidates that pass SANY
                     but fail TLC with a small line diff vs the original

Every attempt is one JSONL row in results/runs/<run-id>/rows.jsonl (Rule 8:
append-only ledger) recording method, model id, prompt hash, budget used, verdict.
Verification is strictly sequential -- one TLC at a time -- per the false-timeout
findings in corpus/configs/TIMEOUT_CONTENTION.md.

Model calls go through the Model interface: AnthropicModel (Messages API over
plain urllib, ANTHROPIC_API_KEY env, no SDK) or LocalStub (deterministic echo of
the input spec; exercises the whole pipeline with zero spend and guarantees the
loop runs to full escalation, since an unchanged spec keeps failing).

CLI: python3 -m harness repair --run-id <id> --specs <list> --model <anthropic|stub> --n <N>
"""
import difflib
import hashlib
import json
import os
import re
import shutil
import time
import urllib.error
import urllib.request
from pathlib import Path

from .mutation import MUTATIONS, apply_mutation
from .runner import (EXPECTED_VIOLATIONS, LIBRARIES, POLICY, PROOF_MODULES, REPO,
                     build_module_index, check_sany, check_tlapm, check_tlc,
                     local_deps, module_name)

BUDGET_FILE = REPO / "corpus" / "configs" / "repair_budget.json"


def load_budget(num: str):
    cfg = json.loads(BUDGET_FILE.read_text())
    b = dict(cfg["defaults"])
    b.update({k: v for k, v in cfg.get("per_spec", {}).get(num, {}).items()
              if not k.startswith("_")})
    return b


# ---------------------------------------------------------------- models

class Model:
    """n candidate completions for a prompt. Implementations must be stateless
    across calls so every row is reproducible from (model id, prompt hash, seed
    semantics of the provider)."""
    id = "abstract"

    def generate(self, prompt: str, n: int, temperature: float, max_tokens: int):
        raise NotImplementedError


class LocalStub(Model):
    """Deterministic no-op: returns the spec embedded in the prompt, unchanged,
    wrapped the way a model reply would be. Tests prompt construction, candidate
    extraction, re-verification, and budget termination without any API spend."""
    id = "local-stub-v1"

    def generate(self, prompt, n, temperature, max_tokens):
        m = re.search(r"===BEGIN SPEC===\n(.*?)\n===END SPEC===", prompt, re.S)
        body = m.group(1) if m else "---- MODULE Empty ----\n===="
        return [body] * n


class AnthropicModel(Model):
    """Messages API over plain HTTPS (no SDK dependency). The API has no n
    parameter, so best-of-N is n sequential calls at the given temperature."""
    API_URL = "https://api.anthropic.com/v1/messages"

    def __init__(self, model_id="claude-sonnet-5"):
        self.id = model_id
        self.key = os.environ.get("ANTHROPIC_API_KEY")
        if not self.key:
            raise SystemExit("ANTHROPIC_API_KEY not set (required for --model anthropic)")

    def _one(self, prompt, temperature, max_tokens):
        req = urllib.request.Request(
            self.API_URL,
            data=json.dumps({
                "model": self.id, "max_tokens": max_tokens, "temperature": temperature,
                "messages": [{"role": "user", "content": prompt}],
            }).encode(),
            headers={"x-api-key": self.key, "anthropic-version": "2023-06-01",
                     "content-type": "application/json"})
        for attempt in range(3):
            try:
                with urllib.request.urlopen(req, timeout=600) as resp:
                    data = json.loads(resp.read())
                return "".join(b.get("text", "") for b in data.get("content", []))
            except urllib.error.HTTPError as e:
                if e.code in (429, 529, 500) and attempt < 2:
                    time.sleep(20 * (attempt + 1))
                    continue
                return f"[api_error {e.code}: {e.read().decode(errors='replace')[:500]}]"
            except urllib.error.URLError as e:
                if attempt < 2:
                    time.sleep(20 * (attempt + 1))
                    continue
                return f"[api_error url: {e}]"

    def generate(self, prompt, n, temperature, max_tokens):
        return [self._one(prompt, temperature, max_tokens) for _ in range(n)]


class OpenAICompatModel(Model):
    """Chat-completions over any OpenAI-compatible endpoint (OpenRouter, Argonne
    routers, vLLM...). Base URL from OPENAI_BASE_URL, key from OPENAI_API_KEY.
    Plain urllib, no SDK. Sequential calls with client-side rate limiting
    (OPENAI_RPM env, default 10 req/min -- the Stage-1 router's limit); n>1 is n
    sequential calls, since provider support for the n parameter is inconsistent.
    Token usage from each response is accumulated on self.usage for cost ledgers."""

    def __init__(self, model_id: str):
        self.id = model_id
        base = os.environ.get("OPENAI_BASE_URL")
        self.key = os.environ.get("OPENAI_API_KEY")
        if not base or not self.key:
            raise SystemExit("OPENAI_BASE_URL and OPENAI_API_KEY must be set "
                             "(required for --model openai:<id>)")
        self.url = base.rstrip("/") + "/chat/completions"
        self.min_interval = 60.0 / float(os.environ.get("OPENAI_RPM", "10"))
        self._last_req = 0.0
        self.usage = {"prompt_tokens": 0, "completion_tokens": 0, "requests": 0}

    def _throttle(self):
        wait = self._last_req + self.min_interval - time.time()
        if wait > 0:
            time.sleep(wait)
        self._last_req = time.time()

    def _one(self, prompt, temperature, max_tokens):
        req = urllib.request.Request(
            self.url,
            data=json.dumps({
                "model": self.id, "max_tokens": max_tokens, "temperature": temperature,
                "messages": [{"role": "user", "content": prompt}],
            }).encode(),
            headers={"Authorization": f"Bearer {self.key}",
                     "content-type": "application/json"})
        for attempt in range(4):
            self._throttle()
            try:
                with urllib.request.urlopen(req, timeout=600) as resp:
                    data = json.loads(resp.read())
                u = data.get("usage") or {}
                self.usage["prompt_tokens"] += u.get("prompt_tokens", 0)
                self.usage["completion_tokens"] += u.get("completion_tokens", 0)
                self.usage["requests"] += 1
                return (data.get("choices") or [{}])[0].get("message", {}).get("content", "") or ""
            except urllib.error.HTTPError as e:
                body = e.read().decode(errors="replace")[:500]
                if e.code in (429, 500, 502, 503, 529) and attempt < 3:
                    time.sleep(30 * (attempt + 1))
                    continue
                return f"[api_error {e.code}: {body}]"
            except (urllib.error.URLError, TimeoutError, OSError) as e:
                if attempt < 3:
                    time.sleep(30 * (attempt + 1))
                    continue
                return f"[api_error url: {e}]"

    def generate(self, prompt, n, temperature, max_tokens):
        return [self._one(prompt, temperature, max_tokens) for _ in range(n)]


def make_model(name: str) -> Model:
    if name == "stub":
        return LocalStub()
    if name == "anthropic":
        return AnthropicModel()
    if name.startswith("anthropic:"):
        return AnthropicModel(name.split(":", 1)[1])
    if name.startswith("openai:"):
        return OpenAICompatModel(name.split(":", 1)[1])
    raise SystemExit(f"unknown model {name!r} "
                     "(want anthropic|anthropic:<id>|openai:<id>|stub)")


# ------------------------------------------------------- fault localization

# TLC trace state header: "State 3: <Copy line 26, col 9 to line 32, col 96 of
# module DistributedReplicatedLog>" (also "<Initial predicate>", "Back to state N:").
STATE_HDR_RE = re.compile(
    r"^(?:Back to state|State) \d+: <(\w+) line (\d+), col \d+ to line (\d+),"
    r" col \d+ of module (\w+)>", re.M)
VIOLATED_RE = re.compile(r"(?:Invariant|Property)\s+(\w+)\s+is violated")
# SANY / TLC error locations: "line 103, col 3 to line 103, col 19 of module Json"
# and SANY parse errors "at line 12, column 5".
ERRLOC_RE = re.compile(r"(?:at )?line (\d+),? col(?:umn)? (\d+)(?: to line (\d+),"
                       r" col \d+ of module (\w+))?")
# Top-level TLA+ definition: flush-left "Name == ..." or "Name(args) == ...".
DEF_RE = re.compile(r"^([A-Za-z_]\w*)(\([^)]*\))?\s*==", re.M)


def extract_definitions(mod_text: str):
    """name -> source block, block spanning from the def line to the next
    flush-left definition or module delimiter. Regex heuristic (no parser):
    misses column-indented defs inside LET or submodules, which is acceptable --
    the fragment is prompt *guidance*, the full spec is in the prompt too."""
    matches = list(DEF_RE.finditer(mod_text))
    blocks = {}
    for i, m in enumerate(matches):
        start = m.start()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(mod_text)
        # stop a block early at a separator/end-of-module line
        sep = re.search(r"^(?:-{4,}|={4,})\s*$", mod_text[start:end], re.M)
        if sep:
            end = start + sep.start()
        blocks[m.group(1)] = mod_text[start:end].rstrip()
    return blocks


def localize(mod_text: str, mod: str, failure_stage: str, evidence: str,
             cfg_text: str, max_chars: int):
    """Map failure evidence back to module source fragments (simple TraceFix-style
    localizer). TLC trace -> the actions named in the trace's state headers (last
    states first) + the violated invariant/property definition. SANY or TLC
    config/runtime error -> +/-8 source lines around each error location that
    names this module (or gives a bare line number). Returns (fragment, names)."""
    frags, names = [], []
    blocks = extract_definitions(mod_text)

    if failure_stage == "tlc":
        for name in VIOLATED_RE.findall(evidence):
            if name not in names:
                names.append(name)
        # property under PROPERTY/PROPERTIES in cfg is where liveness lives even
        # when TLC only says "Temporal properties were violated"
        if "Temporal properties were violated" in evidence:
            for m in re.finditer(r"^\s*PROPERT(?:Y|IES)\b(.*)$", cfg_text, re.M):
                for tok in re.split(r"[,\s]+", m.group(1).strip()):
                    if tok and tok not in names:
                        names.append(tok)
        hdrs = STATE_HDR_RE.findall(evidence)
        for action, _, _, hmod in reversed(hdrs):  # last states first
            if action not in names:
                names.append(action)
        for name in names:
            if name in blocks:
                frags.append(blocks[name])
    if not frags:  # sany / error / nothing matched above
        lines = mod_text.splitlines()
        spans = []
        for m in ERRLOC_RE.finditer(evidence):
            if m.group(4) and m.group(4) != mod:
                continue  # error located in another module (library dep etc.)
            ln = int(m.group(1))
            if 1 <= ln <= len(lines):
                spans.append((max(0, ln - 9), min(len(lines), ln + 8)))
        merged = []
        for lo, hi in sorted(set(spans)):
            if merged and lo <= merged[-1][1]:
                merged[-1] = (merged[-1][0], max(hi, merged[-1][1]))
            else:
                merged.append((lo, hi))
        for lo, hi in merged[:5]:
            frags.append(f"(lines {lo + 1}-{hi})\n" + "\n".join(lines[lo:hi]))
    fragment = "\n\n".join(frags)
    if len(fragment) > max_chars:
        fragment = fragment[:max_chars] + "\n...[fragment truncated]"
    return fragment, names


def truncate_trace(out: str, max_states: int, max_chars: int):
    """Keep the Error lines + the LAST max_states trace states (the fault is
    localized by where the trace ends, TraceFix lesson) + head/tail context."""
    err_lines = [l for l in out.splitlines() if l.startswith("Error")]
    state_starts = [m.start() for m in re.finditer(r"^(?:Back to state|State) \d+:", out, re.M)]
    parts = ["\n".join(err_lines[:6])]
    if state_starts:
        keep_from = state_starts[max(0, len(state_starts) - max_states)]
        trace = out[keep_from:]
        end = re.search(r"^\d+ states generated", trace, re.M)
        if end:
            trace = trace[:end.start()]
        if len(state_starts) > max_states:
            parts.append(f"...[first {len(state_starts) - max_states} trace states omitted]...")
        parts.append(trace.strip())
    else:  # no trace (config error, parse error, ...): head+tail of raw output
        body = out if len(out) <= max_chars else out[:max_chars // 2] + \
            "\n...[truncated]...\n" + out[-max_chars // 2:]
        parts.append(body)
    ev = "\n".join(p for p in parts if p)
    if len(ev) > max_chars:
        ev = ev[:max_chars // 2] + "\n...[truncated]...\n" + ev[-max_chars // 2:]
    return ev


# ---------------------------------------------------------- candidate eval

def resolve_cfg(num: str, cfg_dirs):
    for label, d in cfg_dirs:
        c = d / f"{num}.cfg"
        if c.exists():
            return c.read_text(errors="replace"), label
    return None, None


def baseline_text(num: str, corpus: Path):
    """Same source precedence as runner.eval_spec: committed patch > corpus."""
    patch = REPO / "corpus" / "configs" / "patches" / f"{num}.tla"
    if patch.exists():
        return patch.read_text(errors="replace"), "patched"
    return (corpus / "tla_files" / f"{num}.tla").read_text(errors="replace"), "corpus"


def eval_candidate(num: str, text: str, mod: str, corpus: Path, num2mod, mod2path,
                   cfg_dirs, workroot: Path, timeout: int):
    """Verify one candidate module text through the same SANY/TLC/TLAPS machinery
    and Amendment-1/3 population criterion the oracle uses. Returns (row-fragment,
    failure_stage, evidence, log_text)."""
    row = {"sany": None, "tlc": None, "tlc_vacuity": None,
           "tlaps": None, "budget_used": {}}
    log_parts = []
    cand_mod = module_name(text)
    if cand_mod != mod:
        row["sany"] = "bad_module_name"
        return row, "sany", f"candidate module name {cand_mod!r} != required {mod!r} " \
                            f"(the .cfg and file layout are keyed to {mod!r})", ""
    workdir = workroot / num
    if workdir.exists():
        shutil.rmtree(workdir)
    workdir.mkdir(parents=True)
    (workdir / f"{mod}.tla").write_text(text)
    seen, frontier = set(), local_deps(text, mod2path)
    while frontier:  # corpus-local deps, transitive, patch-aware (as eval_spec)
        d = frontier.pop()
        if d in seen or d == mod:
            continue
        seen.add(d)
        dep_num = mod2path[d].stem
        dep_patch = REPO / "corpus" / "configs" / "patches" / f"{dep_num}.tla"
        dtext = dep_patch.read_text(errors="replace") if dep_patch.exists() \
            else mod2path[d].read_text(errors="replace")
        (workdir / f"{d}.tla").write_text(dtext)
        frontier |= (local_deps(dtext, mod2path) - seen)

    st, out, dt = check_sany(workdir / f"{mod}.tla", workdir, timeout)
    row["sany"] = st
    row["budget_used"]["sany_s"] = round(dt, 1)
    log_parts.append(f"===== SANY ({st}) =====\n{out}")
    failure_stage, evidence = None, None
    if st != "pass":
        failure_stage, evidence = "sany", out

    if st == "pass" and num in LIBRARIES:
        pass  # Amendment 1: library criterion is SANY (+ TLAPS on proved theorems)
    elif st == "pass" and num in PROOF_MODULES:
        pst, proved, total, out, dt = check_tlapm(workdir / f"{mod}.tla", workdir,
                                                  timeout=timeout * 3)
        row["tlaps"] = pst
        row["tlaps_obligations"] = f"{proved}/{total}"
        row["budget_used"]["tlaps_s"] = round(dt, 1)
        log_parts.append(f"===== TLAPS ({pst}, {proved}/{total}) =====\n{out[-8000:]}")
        if pst != "pass":
            failure_stage, evidence = "tlaps", out
    elif st == "pass":
        cfg_text, cfg_origin = resolve_cfg(num, cfg_dirs)
        if cfg_text is None:
            row["tlc"] = "no_cfg"
            failure_stage, evidence = "tlc", "no .cfg available for this spec"
        else:
            (workdir / f"{mod}.cfg").write_text(cfg_text)
            pol = POLICY.get(num, {})
            tlc_mod = mod
            if "wrapper" in pol:  # same two wrapper forms as eval_spec
                w = pol["wrapper"]
                if "corpus_spec" in w:
                    w_num = w["corpus_spec"]
                    w_mod = num2mod[w_num]
                    w_patch = REPO / "corpus" / "configs" / "patches" / f"{w_num}.tla"
                    w_text = w_patch.read_text(errors="replace") if w_patch.exists() \
                        else mod2path[w_mod].read_text(errors="replace")
                else:
                    w_mod = w["module"]
                    w_text = (REPO / w["file"]).read_text()
                if w_mod != mod:  # wrapper EXTENDS the candidate; don't clobber it
                    (workdir / f"{w_mod}.tla").write_text(w_text)
                for d in (local_deps(w_text, mod2path) - seen - {mod}):
                    seen.add(d)
                    (workdir / f"{d}.tla").write_text(
                        mod2path[d].read_text(errors="replace"))
                tlc_mod = w_mod
                (workdir / f"{tlc_mod}.cfg").write_text(cfg_text)
            spec_timeout = max(timeout, pol.get("timeout", 0))
            st2, vac, out, dt = check_tlc(tlc_mod, cfg_text, workdir, spec_timeout,
                                          extra_flags=pol.get("tlc_flags", ()),
                                          jvm_flags=pol.get("jvm_flags", ()))
            expected_prop = EXPECTED_VIOLATIONS.get(num)
            if expected_prop and st2 in ("fail_invariant", "fail_liveness") and \
                    re.search(rf"(?:Invariant|Property)\s+{re.escape(expected_prop)}"
                              r"\s+is violated", out):
                st2, vac = "pass_expected_violation", []
            row["tlc"] = st2
            row["tlc_vacuity"] = ("vacuous:" + ";".join(vac)) if vac else \
                ("clean" if st2 in ("pass", "pass_expected_violation") else None)
            row["cfg_origin"] = cfg_origin
            row["budget_used"]["tlc_s"] = round(dt, 1)
            body = out if len(out) <= 16000 else out[:4000] + "\n...[truncated]...\n" + out[-12000:]
            log_parts.append(f"===== TLC ({st2}, cfg={cfg_origin}) =====\n{body}")
            if st2 not in ("pass", "pass_expected_violation") or vac:
                failure_stage, evidence = "tlc", out

    shutil.rmtree(workroot / num, ignore_errors=True)
    return row, failure_stage, evidence, "\n".join(log_parts)


def verdict_of(num: str, row: dict):
    """Amendment 1/3 population-aware pass criterion, as a single string."""
    if row["sany"] != "pass":
        return f"fail:sany={row['sany']}"
    if num in LIBRARIES:
        return "pass"
    if num in PROOF_MODULES:
        return "pass" if row["tlaps"] == "pass" else f"fail:tlaps={row['tlaps']}"
    if row["tlc"] in ("pass", "pass_expected_violation"):
        if row["tlc_vacuity"] and row["tlc_vacuity"] != "clean":
            return f"fail:{row['tlc_vacuity']}"  # Rule 5: vacuous pass = failure
        return "pass"
    return f"fail:tlc={row['tlc']}"


# ------------------------------------------------------------- the prompt

PROMPT_TEMPLATE = """You are repairing a TLA+ specification so that it passes SANY \
(parser/semantic checker) and its verification criterion ({criterion}). \
The verification setup (the .cfg, any MC wrapper, and all EXTENDed modules) is fixed \
-- you may ONLY change the module below, and its name MUST remain {mod}. Keep the \
change minimal and semantics-preserving with respect to the system being modeled; \
do NOT weaken or delete invariants/properties to force a pass.

=== SPEC (corpus spec {num}, module {mod}) ===
===BEGIN SPEC===
{spec_text}
===END SPEC===

=== MODEL CONFIG (.cfg, read-only) ===
{cfg_text}

=== FAILURE ({failure_stage}: {failure_class}) ===
{evidence}

=== FAULT-LOCALIZED FRAGMENT (definitions implicated by the evidence{names}) ===
{fragment}
{prior_note}
Output the ENTIRE corrected module, nothing else, starting with \
`---- MODULE {mod} ----` and ending with `====`."""


def build_prompt(num, mod, text, cfg_text, failure_stage, failure_class, evidence,
                 fragment, names, budget, prior_note=""):
    spec_text = text if len(text) <= budget["spec_max_chars"] else \
        text[:budget["spec_max_chars"]] + "\n...[spec truncated]"
    if num in PROOF_MODULES:
        criterion = "all TLAPS proof obligations proved"
    elif num in LIBRARIES:
        criterion = "SANY semantic check of the operator library"
    elif num in EXPECTED_VIOLATIONS:
        criterion = (f"TLC must find a violation of {EXPECTED_VIOLATIONS[num]} "
                     "specifically -- this spec is DESIGNED to violate it")
    else:
        criterion = "non-vacuous TLC model check"
    return PROMPT_TEMPLATE.format(
        num=num, mod=mod, spec_text=spec_text, cfg_text=(cfg_text or "(none)").strip(),
        failure_stage=failure_stage, failure_class=failure_class,
        evidence=evidence, fragment=fragment or "(no fragment localized)",
        names=(": " + ", ".join(names[:8])) if names else "",
        criterion=criterion, prior_note=prior_note)


CANDIDATE_RE = re.compile(r"(-{4,}\s*MODULE\s+\w+\s*-{4,}.*?^={4,})", re.S | re.M)


def extract_candidate(reply: str):
    m = CANDIDATE_RE.findall(reply or "")
    return m[-1] if m else None


def diff_lines(a: str, b: str):
    return sum(1 for l in difflib.unified_diff(a.splitlines(), b.splitlines(),
                                               lineterm="", n=0)
               if l[:1] in "+-" and l[:3] not in ("+++", "---"))


# ------------------------------------------------------------- repair loop

def repair_spec(num, corpus, num2mod, mod2path, cfg_dirs, workroot, rundir, model,
                n_override=None):
    budget = load_budget(num)
    if n_override:
        budget["best_of_n"] = n_override
    timeout = budget["timeout_s"]
    logdir = rundir / "logs"
    canddir = rundir / "candidates"
    rows, t0 = [], time.time()
    mod = num2mod.get(num)
    orig, origin = baseline_text(num, corpus)
    # diff base normalized to the module block only: some corpus files carry long
    # prose AFTER the terminating ==== (e.g. spec 78's "Tips & Tricks"), which TLA+
    # ignores but which would inflate candidate_diff_lines (extract_candidate
    # canonicalizes model replies to the module block) and wrongly disqualify
    # near-misses from the mutation pass.
    orig_norm = extract_candidate(orig) or orig
    cfg_text, _ = resolve_cfg(num, cfg_dirs)

    def emit(method, attempt, row_frag, prompt=None, extra=None, log_text=""):
        row = {"spec": num, "method": method, "model": model.id, "attempt": attempt,
               "prompt_sha256": hashlib.sha256(prompt.encode()).hexdigest() if prompt else None,
               **row_frag}
        row["verdict"] = verdict_of(num, row_frag) if row_frag.get("sany") else "invalid_candidate"
        row["budget"] = {k: budget[k] for k in
                         ("iterative_rounds", "best_of_n", "mutation_pass", "timeout_s")}
        row["spec_elapsed_s"] = round(time.time() - t0, 1)
        if extra:
            row.update(extra)
        lp = logdir / f"{num}-{method}-{attempt}.log"
        lp.write_text(log_text or "no log\n")
        row["log_path"] = str(lp)
        rows.append(row)
        return row

    if not mod:
        emit("repair-baseline", 0, {"sany": "no_module_header", "budget_used": {}})
        return rows

    def run_candidate(text, method, attempt, prompt=None, extra=None):
        (canddir / f"{num}-{method}-{attempt}.tla").write_text(text)
        row_frag, fstage, fev, log_text = eval_candidate(
            num, text, mod, corpus, num2mod, mod2path, cfg_dirs, workroot, timeout)
        row = emit(method, attempt, row_frag, prompt=prompt, extra=extra, log_text=log_text)
        row["candidate_diff_lines"] = diff_lines(orig_norm, extract_candidate(text) or text)
        return row, fstage, fev

    # -- baseline (the failure evidence everything else consumes)
    brow, fstage, fev = run_candidate(orig, "repair-baseline", 0,
                                      extra={"source_origin": origin})
    if brow["verdict"] == "pass":
        return rows

    near_misses = []  # (label, text) candidates for the mutation pass

    def note_near_miss(label, text, row):
        norm = extract_candidate(text) or text
        if row.get("sany") == "pass" and row["verdict"].startswith("fail:tlc") and \
                diff_lines(orig_norm, norm) <= budget["near_miss_max_diff_lines"] and \
                all(t != norm for _, t in near_misses):
            near_misses.append((label, norm))

    note_near_miss("baseline", orig, brow)

    def make_repair_prompt(cur_text, cur_stage, cur_ev, prior_note=""):
        evidence = truncate_trace(cur_ev or "", budget["trace_max_states"],
                                  budget["evidence_max_chars"])
        ev_lines = [l for l in (cur_ev or "").strip().splitlines() if l.strip()]
        err_lines = [l for l in ev_lines if re.search(r"error", l, re.I)]
        fclass = (err_lines or ev_lines or ["unknown"])[0].strip()[:120]
        fragment, names = localize(cur_text, mod, cur_stage or "error", cur_ev or "",
                                   cfg_text or "", budget["fragment_max_chars"])
        return build_prompt(num, mod, cur_text, cfg_text, cur_stage or "error",
                            fclass, evidence, fragment, names, budget,
                            prior_note=prior_note)

    total_candidates = 1

    # -- iterative rounds (<=2), each fed the previous candidate's own failure
    cur_text, cur_stage, cur_ev, prior_note = orig, fstage, fev, ""
    for r in range(1, budget["iterative_rounds"] + 1):
        if total_candidates >= budget["max_candidates_total"]:
            break
        prompt = make_repair_prompt(cur_text, cur_stage, cur_ev, prior_note)
        mt0 = time.time()
        reply = model.generate(prompt, 1, budget["temperature_rounds"],
                               budget["max_tokens"])[0]
        cand = extract_candidate(reply)
        total_candidates += 1
        if cand is None:
            emit(f"repair-r{r}", 0, {"sany": None, "budget_used":
                 {"model_s": round(time.time() - mt0, 1)}}, prompt=prompt,
                 log_text=f"no module block in model reply:\n{(reply or '')[:4000]}")
            prior_note = ("\nNOTE: your previous reply contained no parseable "
                          "module block; output ONLY the module.\n")
            continue
        row, nstage, nev = run_candidate(cand, f"repair-r{r}", 0, prompt=prompt)
        row["budget_used"]["model_s"] = round(time.time() - mt0, 1)
        if row["verdict"] == "pass":
            return rows
        note_near_miss(f"r{r}", cand, row)
        if nev:  # iterate on the new candidate's own failure
            cur_text, cur_stage, cur_ev = cand, nstage, nev
            prior_note = ("\nNOTE: this spec is already the result of a previous "
                          "repair attempt that still fails as shown above.\n")

    # -- best-of-N sampling against the ORIGINAL failure (independent samples)
    prompt = make_repair_prompt(orig, fstage, fev)
    n = min(budget["best_of_n"], budget["max_candidates_total"] - total_candidates)
    if n > 0:
        mt0 = time.time()
        replies = model.generate(prompt, n, budget["temperature_best_of_n"],
                                 budget["max_tokens"])
        model_s = round(time.time() - mt0, 1)
        for i, reply in enumerate(replies, 1):
            total_candidates += 1
            cand = extract_candidate(reply)
            if cand is None:
                emit("repair-bestofN", i, {"sany": None, "budget_used":
                     {"model_s": model_s if i == 1 else 0}}, prompt=prompt,
                     log_text=f"no module block in model reply:\n{(reply or '')[:4000]}")
                continue
            row, _, _ = run_candidate(cand, "repair-bestofN", i, prompt=prompt)
            if i == 1:
                row["budget_used"]["model_s"] = model_s
            if row["verdict"] == "pass":
                return rows
            note_near_miss(f"bestofN-{i}", cand, row)

    # -- symbolic mutation pass on near-misses (SpecGen lesson: small syntactic
    # operator swaps close specs that are one token away from correct)
    if budget["mutation_pass"]:
        attempt = 0
        for label, base in near_misses:
            for mlabel, regex, repl in MUTATIONS:
                if total_candidates >= budget["max_candidates_total"]:
                    break
                mutant, nsubs = apply_mutation(base, regex, repl)
                if mutant is None or mutant == base:
                    continue
                attempt += 1
                total_candidates += 1
                row, _, _ = run_candidate(mutant, "repair-mutation", attempt,
                                          extra={"mutation": mlabel,
                                                 "mutated_from": label,
                                                 "substitutions": nsubs})
                if row["verdict"] == "pass":
                    return rows
    return rows


# --------------------------------------------------------------- the sweep

def run_repair(corpus: Path, run_id: str, model_name: str, specs=None, n=None):
    rundir = REPO / "results" / "runs" / run_id
    if (rundir / "rows.jsonl").exists():
        raise SystemExit(f"{rundir} already has rows.jsonl -- runs are append-only "
                         "per-run directories (Rule 8); pick a new --run-id")
    (rundir / "logs").mkdir(parents=True, exist_ok=True)
    (rundir / "candidates").mkdir(exist_ok=True)
    workroot = Path("/tmp/prove-tla-repair") / run_id
    model = make_model(model_name)
    num2mod, mod2path = build_module_index(corpus)
    cfg_dirs = [("override", REPO / "corpus" / "configs" / "overrides"),
                ("original", corpus / "cfg"),
                ("draft", REPO / "corpus" / "configs" / "drafts")]
    all_nums = sorted({p.stem for p in (corpus / "descriptions").glob("*.json")}, key=int)
    todo = [x for x in all_nums if not specs or x in specs]

    (rundir / "config.json").write_text(json.dumps({
        "run_id": run_id, "corpus": str(corpus), "method_family": "repair",
        "model": model.id, "n_specs": len(todo),
        "budget_config": json.loads(BUDGET_FILE.read_text()),
        "budget_config_sha256": hashlib.sha256(BUDGET_FILE.read_bytes()).hexdigest(),
        "sequential": True, "note": "one verification at a time (TIMEOUT_CONTENTION.md)",
    }, indent=2))

    summary = {}
    with open(rundir / "rows.jsonl", "w") as fh:
        for i, num in enumerate(todo, 1):
            rows = repair_spec(num, corpus, num2mod, mod2path, cfg_dirs, workroot,
                               rundir, model, n_override=n)
            for r in rows:
                fh.write(json.dumps(r) + "\n")
            fh.flush()
            passed = [r for r in rows if r["verdict"] == "pass"]
            summary[num] = passed[0]["method"] if passed else \
                (rows[-1]["verdict"] if rows else "no_rows")
            print(f"[{i}/{len(todo)}] spec {num}: {summary[num]} "
                  f"({len(rows)} attempts, {rows[-1]['spec_elapsed_s'] if rows else 0}s)")

    # Rule 3: pass@1 (baseline excluded; first model round only) vs pass@N separately
    pass_at_1 = sum(1 for v in summary.values() if v in ("repair-baseline", "repair-r1"))
    pass_any = sum(1 for v in summary.values() if v.startswith("repair-"))
    baseline_pass = sum(1 for v in summary.values() if v == "repair-baseline")
    (rundir / "summary.json").write_text(json.dumps({
        "per_spec": summary, "n": len(todo), "baseline_pass": baseline_pass,
        "pass_at_1_incl_baseline": pass_at_1, "pass_at_full_budget": pass_any,
        "token_usage": getattr(model, "usage", None),
    }, indent=2))
    print(f"\n=== {run_id}: {len(todo)} specs, model={model.id} ===")
    print(f"  baseline pass (no repair needed): {baseline_pass}")
    print(f"  pass@1 (baseline+r1):             {pass_at_1}")
    print(f"  pass@full-budget:                 {pass_any}")
    shutil.rmtree(workroot, ignore_errors=True)
    return summary
