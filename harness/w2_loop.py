"""W2.2 -- the RFT generation ("Ralph") loop.

Design: docs/superpowers/specs/2026-07-09-w21-quality-corpus-design.md,
Workstream 2. Per gold seed spec: spec -> NL (back-translation) -> the NL
becomes a generation seed -> NL -> spec' (property-frozen generation, gated
by SANY + non-vacuous TLC + the deterministic mutation battery), iterating
with repair-context feedback up to max_iters. Survivors re-pass decontam
before being recorded.

Model calls go through the same `Model` interface as harness.repair
(`.generate(prompt, n, temperature, max_tokens) -> list[str]`) -- this module
never talks to a model directly; the caller injects a Model (real or fake),
which is what keeps every test in test_w2_loop.py free of live Sophia spend.

Reuses (does not modify):
  harness.runner       check_sany, check_tlc, module_name, vacuity_flags (via check_tlc)
  harness.mutation      run_mutation_on_module
  harness.adequacy      structural_features, complexity_score, quality_label
  harness.corpora       shingle_set, normalize_tla, nearest_similarity, SHINGLE_K,
                        NEAR_DUP_THRESHOLD
  harness.w21_funnel    load_canonical (decontam corpus: bench + examples;
                        holdout-30 is a subset of bench, see project memory)
  harness.gen_eval      extract_module (module-block extraction reused, not
                        rewritten -- extract_module_and_cfg below layers a cfg
                        block extraction on top of it)

Quality gates (2026-07-10 audit fixes S1/S4/S6/E1) -- all HARD METRICS, no
LLM-judge/opinion scoring anywhere (Eric's rule):

  FIX 1 (mutation floor, starve-proof): the deterministic mutation battery
    runs on every TLC-passing candidate. no-site -> accept (tag "no_site");
    kills but ALL TypeOK-style -> reject "typeok_only_invariant" and iterate
    (the S4 gaming surface: the model writes its own cfg, so an invariant
    that only catches type errors checks nothing); sites-but-no-kills ->
    accept (tag "no_kill", weak signal, recorded not punished); any real
    safety catch -> accept (tag "safety_catch").
  FIX 2 (cfg invariant-name gate): the cfg must declare at least one
    INVARIANT whose name does not match /type/i -- TypeOK-only cfgs fail
    fast, before any TLC spend.
  FIX 3 (NL<->invariant correspondence, STRUCTURAL): the back-translated NL
    must contain a "SAFETY PROPERTY:" section (parse_nl raises
    NLMissingProperty otherwise -> seed skipped); the generation reply must
    carry "PROPERTY_INVARIANT: <Name>" naming the invariant implementing THE
    NL property; the loop verifies that name is defined in the module,
    listed as INVARIANT in the cfg, and not TypeOK-style-named. LIMITATION,
    stated plainly: this pins the (NL property <-> checked invariant)
    LINKAGE structurally -- it does NOT verify that the invariant's TLA+
    body semantically means what the NL prose promises (impossible without
    an LLM judge, which is banned). What it buys: the RFT pair can no longer
    silently train on an invariant unrelated to the NL's promise.
  FIX 4 (liveness gate, honest cheap version): if the module uses liveness
    operators (<>, []<>, WF_, SF_ -- NOT the bare [][Next]_v safety
    skeleton) but the cfg checks no PROPERTY, gate-fail "liveness_unchecked"
    (either check it or drop the unused fairness). If the cfg checks a
    PROPERTY, TLC already verifies it; liveness_checked=true is recorded.
    Liveness is NOT required on every spec -- safety-only specs are fine.
  FIX 5 (required liveness + stutter-vacuity, 2026-07-23, opt-in via
    require_liveness=True -- W4 liveness cells): the cfg must check a
    PROPERTY; at least one checked property must be an eventuality (<> or
    ~>) defined in the module; and TLC is re-run on the fairness-free
    closure (strip_fairness) where the property MUST fail -- an eventuality
    that survives infinite stuttering is trivially true and is rejected
    "liveness_stutter_trivial". Survivors record liveness_property and
    stutter_check ("nontrivial", or "inconclusive:<status>" when the
    stutter run times out -- recorded not punished, no_kill philosophy).

CLI:
  python3 -m harness.w2_loop --seeds data/chattla-corpora-v2/manifest_w2_seeds.jsonl \\
      --raw /Users/eric/GitHub/tla-dataset-pipeline/data/raw \\
      --run-dir results/runs/w2-<date> [--seed-cap N] [--k N] [--model NAME] [--dry-run]
  python3 -m harness.w2_loop --report-dirs results/runs/w2-a results/runs/w2-b
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
from pathlib import Path

from .adequacy import complexity_score, structural_features
from .corpora import NEAR_DUP_THRESHOLD, SHINGLE_K, nearest_similarity, normalize_tla, shingle_set
from .gen_eval import extract_module
from .mutation import run_mutation_on_module
from .runner import check_sany, check_tlc, module_name

DEFAULT_MAX_ITERS = 8
DEFAULT_TIMEOUT_S = 90


# --------------------------------------------------------------- prompts

def backtranslate_prompt(spec_text: str, cfg_text: str) -> str:
    """Stage 1: spec -> NL back-translation prompt. Asks the model for a
    precise natural-language system description (including the safety
    property) with NO TLA+ syntax in the reply -- the NL becomes a
    generation seed later, so it must stand alone as an English spec."""
    return (
        "You are given a verified TLA+ specification and its TLC model-checker "
        "configuration below. Write a precise NATURAL LANGUAGE description of "
        "the system it models: what the variables represent, what each action "
        "does, and what the safety property (the invariant) guarantees. "
        "Do NOT use any TLA+ syntax, operators, or code in your answer -- plain "
        "English only, as if briefing an engineer who will re-implement the "
        "system from your description alone.\n\n"
        "Your description MUST end with an explicit section on its own line "
        "starting exactly with `SAFETY PROPERTY:` that states, in prose, the "
        "safety property the invariant guarantees. A description without that "
        "section will be discarded.\n\n"
        "===BEGIN SPEC===\n" + spec_text + "\n===END SPEC===\n\n"
        "===BEGIN CFG===\n" + cfg_text + "\n===END CFG===\n\n"
        "Natural language description:"
    )


_FENCE_RE = re.compile(r"```(?:\w+)?\n(.*?)```", re.S)


class NLMissingProperty(Exception):
    """Raised by parse_nl when the back-translated NL lacks the required
    `SAFETY PROPERTY:` section (FIX 3a) -- without it the NL<->invariant
    fidelity contract has nothing to anchor on, so the seed is skipped
    (rejection_reason='nl_missing_property') rather than run blind."""


def parse_nl(reply: str) -> str:
    """Extract the natural-language description from a back-translation
    reply, stripping markdown fences if the model wrapped its answer in one.
    FIX 3a: raises NLMissingProperty if there is no `SAFETY PROPERTY:`
    section -- the structural anchor for the invariant-fidelity contract."""
    m = _FENCE_RE.search(reply)
    text = (m.group(1) if m else reply).strip()
    if "SAFETY PROPERTY:" not in text:
        raise NLMissingProperty("back-translated NL lacks a 'SAFETY PROPERTY:' section")
    return text


def generation_prompt(nl_description: str, module_name: str, error_context: str | None = None) -> str:
    """Stage 2: NL -> spec' generation prompt (property-freeze -> gen). The
    model MUST emit both a TLA+ module AND its .cfg in one reply -- the
    simplest honest contract for a spec that needs a .cfg to TLC-check.
    error_context, if given, is prior-iteration SANY/TLC evidence fed back as
    repair context (Ralph-loop iteration)."""
    parts = [
        "Write a TLA+ specification that implements EXACTLY the system "
        "described below, and a TLC .cfg to model-check it. The system's "
        "safety property described in the NL text must be captured as a real, "
        "non-trivial INVARIANT (not `Inv == TRUE`) in the .cfg.\n\n"
        f"Name the module `{module_name}`.\n\n"
        "===BEGIN NATURAL LANGUAGE DESCRIPTION===\n" + nl_description +
        "\n===END NATURAL LANGUAGE DESCRIPTION===\n\n"
        "Reply with exactly one TLA+ module in a ```tla fenced block and "
        "exactly one .cfg in a ```cfg fenced block. After the two blocks, "
        "add exactly one line of the form `PROPERTY_INVARIANT: <Name>` naming "
        "the invariant in your module that implements THE safety property "
        "stated in the description's SAFETY PROPERTY section. That name must "
        "be defined in the module, listed as an INVARIANT in the .cfg, and "
        "must be a semantic safety invariant (not a TypeOK-style "
        "type-correctness check)."
    ]
    if error_context:
        parts.append(
            "\n\nYour previous attempt failed verification. Fix it using this "
            "error evidence:\n" + error_context
        )
    return "\n".join(parts)


_CFG_FENCE_RE = re.compile(r"```cfg\n(.*?)```", re.S)
_ANY_FENCE_RE = re.compile(r"```(?:\w+)?\n(.*?)```", re.S)


def extract_module_and_cfg(reply: str):
    """Pull (module_text, cfg_text) out of a generation reply. Module
    extraction reuses harness.gen_eval.extract_module (not rewritten). cfg
    extraction looks for a ```cfg fenced block first, falling back to any
    fenced block that looks like a TLC config (has an INIT/NEXT/SPECIFICATION
    line) and isn't the module block itself."""
    mod = extract_module(reply)
    cfg_m = _CFG_FENCE_RE.search(reply)
    if cfg_m:
        return mod, cfg_m.group(1).strip()
    for m in _ANY_FENCE_RE.finditer(reply):
        block = m.group(1).strip()
        if mod and block == mod:
            continue
        if re.search(r"^\s*(INIT|NEXT|SPECIFICATION|INVARIANT)\b", block, re.M):
            return mod, block
    return mod, None


_PI_LINE_RE = re.compile(r"^\s*PROPERTY_INVARIANT:\s*(\w+)\s*$", re.M)


def parse_property_invariant(reply: str):
    """FIX 3b: the `PROPERTY_INVARIANT: <Name>` line naming which invariant
    implements the NL's safety property. None if absent."""
    m = _PI_LINE_RE.search(reply)
    return m.group(1) if m else None


# Mirrors harness.mutation._TYPE_NAME_RE (private there; mirrored per the
# audit instruction): TypeOK-style names assert well-typedness only.
_TYPE_NAME_RE = re.compile(r"type", re.IGNORECASE)
_CFG_INVARIANT_RE = re.compile(r"^\s*INVARIANTS?\b(.*)$", re.M)


def cfg_invariant_names(cfg_text: str) -> list:
    """All names listed under INVARIANT(S) in a TLC cfg, in order."""
    names = []
    for m in _CFG_INVARIANT_RE.finditer(cfg_text or ""):
        for tok in re.split(r"[,\s]+", m.group(1).strip()):
            if tok:
                names.append(tok)
    return names


def semantic_invariant_names(cfg_text: str) -> list:
    """FIX 2: the cfg's declared invariants whose names do NOT match /type/i.
    Empty list = the cfg checks only type-correctness (or nothing) -- the
    cheap S4 gate: a model writing its own cfg can't pass with TypeOK alone."""
    return [n for n in cfg_invariant_names(cfg_text) if not _TYPE_NAME_RE.search(n)]


# FIX 4 liveness detector: diamond <> (not the << >> tuple brackets), []<>,
# WF_/SF_ fairness. Deliberately NOT bare [] -- every safety spec's
# [][Next]_v skeleton contains it and is not liveness.
_LIVENESS_RE = re.compile(r"(?<!<)<>(?!>)|WF_|SF_")


def uses_liveness_operators(mod_text: str) -> bool:
    return bool(_LIVENESS_RE.search(mod_text or ""))


_CFG_PROPERTY_RE = re.compile(r"^\s*PROPERT(?:Y|IES)\b", re.M)
_CFG_PROPERTY_NAMES_RE = re.compile(r"^\s*PROPERT(?:Y|IES)\b(.*)$", re.M)


def cfg_property_names(cfg_text: str) -> list:
    """All names listed under PROPERTY/PROPERTIES in a TLC cfg, in order."""
    names = []
    for m in _CFG_PROPERTY_NAMES_RE.finditer(cfg_text or ""):
        for tok in re.split(r"[,\s]+", m.group(1).strip()):
            if tok:
                names.append(tok)
    return names


# FIX 5 eventuality detector: diamond <> or leads-to ~> in the property's
# definition body. A PROPERTY that is only [](...) is safety-shaped and does
# not satisfy a liveness requirement.
_EVENTUALITY_RE = re.compile(r"(?<!<)<>(?!>)|~>")


def definition_body(mod_text: str, name: str) -> str:
    """The text of `name == ...` up to the next top-level definition or module
    end. Empty string if not defined. Textual, not parsed -- same fidelity
    level as the other structural gates."""
    m = re.search(rf"^\s*{re.escape(name)}(?:\([^)]*\))?\s*==", mod_text or "", re.M)
    if not m:
        return ""
    rest = mod_text[m.end():]
    stop = re.search(r"^\w[\w!]*(?:\([^)]*\))?\s*==|^====", rest, re.M)
    return rest[:stop.start()] if stop else rest


def strip_fairness(mod_text: str):
    """Remove every WF_/SF_ fairness application (and the /\\ that conjoins
    it) from the module text. Returns (stripped_text, n_removed). Paren-
    balanced textual scan -- handles WF_<<x, y>>(A(b)). Used by the FIX 5
    stutter-vacuity check: a liveness PROPERTY that still passes TLC on the
    fairness-free closure never needed fairness and is stutter-trivial."""
    out, n, i = [], 0, 0
    text = mod_text or ""
    while True:
        m = re.search(r"(?:/\\\s*)?(?:WF|SF)_", text[i:])
        if not m:
            out.append(text[i:])
            break
        start = i + m.start()
        j = i + m.end()
        # subscript: identifier or <<...>> tuple, up to the opening paren
        while j < len(text) and text[j] != "(":
            j += 1
        depth = 0
        while j < len(text):
            if text[j] == "(":
                depth += 1
            elif text[j] == ")":
                depth -= 1
                if depth == 0:
                    j += 1
                    break
            j += 1
        out.append(text[i:start])
        n += 1
        i = j
    return "".join(out), n


# --------------------------------------------------------------- loop

def _evidence(sany_out: str | None, tlc_status: str | None, tlc_out: str | None,
              vac: list | None, note: str | None = None) -> str:
    parts = []
    if note:
        parts.append(note)
    if sany_out is not None:
        parts.append("SANY output (truncated):\n" + sany_out[-1500:])
    if tlc_status is not None:
        parts.append(f"TLC status: {tlc_status}")
        if tlc_out:
            parts.append("TLC output (truncated):\n" + tlc_out[-1500:])
    if vac:
        parts.append("Vacuity flags: " + ", ".join(vac))
    return "\n".join(parts)


def run_loop_for_seed(model, nl: str, module_name_: str, workdir: Path, timeout: int,
                       max_iters: int = DEFAULT_MAX_ITERS,
                       require_liveness: bool = False) -> dict:
    """Property-freeze the NL (it is passed in already frozen -- the caller
    generates it once via backtranslate_prompt/parse_nl and reuses it across
    all iters of this seed) and iterate: generate -> SANY -> TLC (needs a
    cfg the model must emit) -> vacuity/thin gates -> deterministic mutation
    battery with the FIX-1 starve-proof floor (no-site/no-kill accepted and
    tagged; typeok-only kills rejected -- see module docstring) -> converged
    survivor or iterate with error evidence fed back as repair context.
    Also gates (pre-SANY, cheap): PROPERTY_INVARIANT line present/defined/
    listed/non-TypeOK (FIX 3), cfg has a semantic invariant (FIX 2); and the
    liveness gate (FIX 4). Returns a result dict."""
    # MUST be absolute: check_sany/check_tlc build java-side paths (jtmp,
    # -metadir) from this dir; with a relative workdir SANY's module search
    # path resolves against a doubled prefix and even standard modules
    # (Naturals) come back fail_missing_module. Found live: first Sophia smoke
    # was 0/5 all-sany_fail purely from this (the specs were SANY-clean).
    workdir = Path(workdir).resolve()
    workdir.mkdir(parents=True, exist_ok=True)
    error_context = None
    last_reason = "unknown"

    for it in range(1, max_iters + 1):
        prompt = generation_prompt(nl, module_name_, error_context=error_context)
        [reply] = model.generate(prompt, 1, 0.8, 8192)
        mod_text, cfg_text = extract_module_and_cfg(reply)

        if mod_text is None:
            last_reason = "no_module_in_reply"
            error_context = _evidence(None, None, None, None,
                                       note="Your reply did not contain a parseable "
                                            "```tla fenced module block. Emit exactly one.")
            continue
        if cfg_text is None:
            last_reason = "no_cfg_in_reply"
            error_context = _evidence(None, None, None, None,
                                       note="Your reply did not contain a parseable "
                                            "```cfg fenced .cfg block. Emit exactly one.")
            continue

        # FIX 3c: invariant-fidelity contract (structural; see module docstring
        # for the stated limitation -- linkage, not deep semantics).
        pi = parse_property_invariant(reply)
        if pi is None:
            last_reason = "property_invariant_missing"
            error_context = _evidence(None, None, None, None,
                                       note="Your reply is missing the required line "
                                            "`PROPERTY_INVARIANT: <Name>` naming the "
                                            "invariant that implements the SAFETY "
                                            "PROPERTY from the description.")
            continue

        # FIX 2: cfg must declare at least one semantic (non-TypeOK-named)
        # invariant -- cheap gate, fires before any TLC spend.
        if not semantic_invariant_names(cfg_text):
            last_reason = "no_semantic_invariant_in_cfg"
            error_context = _evidence(None, None, None, None,
                                       note="Your .cfg declares no semantic safety "
                                            "invariant -- declare and check a semantic "
                                            "safety invariant, not only type-correctness "
                                            "(TypeOK-style invariants do not count).")
            continue

        if _TYPE_NAME_RE.search(pi):
            last_reason = "property_invariant_typeok_named"
            error_context = _evidence(None, None, None, None,
                                       note=f"PROPERTY_INVARIANT names `{pi}`, a "
                                            "TypeOK-style type-correctness check. The "
                                            "safety property from the description must "
                                            "be a semantic invariant, not a type check.")
            continue
        if not re.search(rf"^\s*{re.escape(pi)}(?:\([^)]*\))?\s*==", mod_text, re.M):
            last_reason = "property_invariant_not_defined"
            error_context = _evidence(None, None, None, None,
                                       note=f"PROPERTY_INVARIANT names `{pi}` but the "
                                            "module does not define it.")
            continue
        if pi not in cfg_invariant_names(cfg_text):
            last_reason = "property_invariant_not_in_cfg"
            error_context = _evidence(None, None, None, None,
                                       note=f"PROPERTY_INVARIANT names `{pi}` but the "
                                            ".cfg does not list it under INVARIANT.")
            continue

        # FIX 4: liveness gate -- fairness/temporal ops in the module with no
        # PROPERTY in the cfg means the liveness claim is decorative.
        liveness_checked = bool(_CFG_PROPERTY_RE.search(cfg_text))
        if uses_liveness_operators(mod_text) and not liveness_checked:
            last_reason = "liveness_unchecked"
            error_context = _evidence(None, None, None, None,
                                       note="Your module uses liveness/fairness "
                                            "operators (<>, WF_, SF_) but the .cfg "
                                            "checks no PROPERTY. Either add a PROPERTY "
                                            "line to the .cfg to check the liveness "
                                            "claim, or drop the unused fairness/"
                                            "temporal operators.")
            continue

        # FIX 5 (required liveness, static half): when the caller demands a
        # liveness property (W4 liveness cells), the cfg must check a PROPERTY
        # and at least one checked property must be an eventuality (<> or ~>)
        # defined in the module. Cheap, fires before any TLC spend.
        liveness_property = None
        if require_liveness:
            prop_names = cfg_property_names(cfg_text)
            if not prop_names:
                last_reason = "liveness_property_missing"
                error_context = _evidence(None, None, None, None,
                                           note="This cell REQUIRES a liveness property: "
                                                "define a temporal property (an "
                                                "eventuality using <> or ~>) in the "
                                                "module, add fairness (WF_/SF_) to Spec, "
                                                "and check it with a PROPERTY line in "
                                                "the .cfg.")
                continue
            eventualities = [p for p in prop_names
                             if _EVENTUALITY_RE.search(definition_body(mod_text, p))]
            if not eventualities:
                last_reason = "temporal_property_not_eventuality"
                error_context = _evidence(None, None, None, None,
                                           note=f"The checked PROPERTY {prop_names} is "
                                                "not an eventuality -- a []-only formula "
                                                "is safety-shaped. The liveness property "
                                                "must contain <> or ~> so it promises "
                                                "real progress.")
                continue
            liveness_property = eventualities[0]

        mod = module_name(mod_text) or module_name_
        iter_dir = workdir / f"iter{it}"
        if iter_dir.exists():
            shutil.rmtree(iter_dir)
        iter_dir.mkdir(parents=True)
        tla_path = iter_dir / f"{mod}.tla"
        cfg_path = iter_dir / f"{mod}.cfg"
        tla_path.write_text(mod_text)
        cfg_path.write_text(cfg_text)

        sany_status, sany_out, _ = check_sany(tla_path, iter_dir, timeout)
        if sany_status != "pass":
            last_reason = f"sany_{sany_status}"
            error_context = _evidence(sany_out, None, None, None,
                                       note=f"SANY {sany_status}.")
            continue

        tlc_status, vac, tlc_out, _ = check_tlc(mod, cfg_text, iter_dir, timeout)
        if tlc_status != "pass":
            last_reason = f"tlc_{tlc_status}"
            error_context = _evidence(sany_out, tlc_status, tlc_out, None)
            continue

        distinct_states = None
        m = re.search(r"(\d+) distinct states found", tlc_out)
        if m:
            distinct_states = int(m.group(1))

        if vac:
            last_reason = "vacuous: " + ", ".join(vac)
            error_context = _evidence(sany_out, tlc_status, tlc_out, vac,
                                       note="The spec passed TLC but is vacuous "
                                            "(trivial invariant, no real property "
                                            "checked, or a degenerate state space). "
                                            "Fix the invariant/property to be real "
                                            "and meaningful.")
            continue
        if distinct_states is not None and distinct_states < 3:
            last_reason = f"thin_model: {distinct_states} states"
            error_context = _evidence(sany_out, tlc_status, tlc_out, vac,
                                       note=f"Only {distinct_states} distinct states "
                                            "were generated -- the model is too thin. "
                                            "Add real behavioral variety.")
            continue

        # FIX 5 (required liveness, dynamic half): stutter-vacuity check.
        # Re-run TLC on the fairness-free closure (WF_/SF_ stripped). A real
        # liveness property MUST fail there -- stuttering forever at any state
        # violates any honest eventuality. If it still passes, the property
        # never needed fairness and is trivially true (e.g. <> of an
        # Init-true predicate): reject "liveness_stutter_trivial". A module
        # with no fairness at all whose PROPERTY passed the main run is the
        # same defect. Timeout/other on the stutter run is recorded
        # "inconclusive" and accepted (no_kill philosophy: weak signal,
        # recorded not punished). Runs before the mutation battery so the
        # cheap single TLC run fires first.
        stutter_check = None
        if require_liveness:
            stripped, n_fair = strip_fairness(mod_text)
            if n_fair == 0:
                last_reason = "liveness_stutter_trivial"
                error_context = _evidence(None, None, None, None,
                                           note="Your PROPERTY passed TLC but Spec has "
                                                "no WF_/SF_ fairness, so the property "
                                                "holds even if the system stutters "
                                                "forever -- it promises nothing. Write "
                                                "an eventuality that is FALSE without "
                                                "fairness and add the fairness that "
                                                "makes it true.")
                continue
            st_dir = iter_dir / "stutter"
            st_dir.mkdir(parents=True, exist_ok=True)
            (st_dir / f"{mod}.tla").write_text(stripped)
            (st_dir / f"{mod}.cfg").write_text(cfg_text)
            st_status, _, st_out, _ = check_tlc(mod, cfg_text, st_dir, timeout)
            if st_status == "pass":
                last_reason = "liveness_stutter_trivial"
                error_context = _evidence(None, None, None, None,
                                           note=f"Stutter-vacuity check: PROPERTY "
                                                f"{liveness_property} still holds with "
                                                "ALL fairness stripped from Spec -- it "
                                                "is trivially true (holds even if the "
                                                "system stops forever) and checks no "
                                                "real progress. Strengthen it so it "
                                                "requires the fairness to hold.")
                continue
            stutter_check = ("nontrivial" if st_status.startswith("fail")
                             else f"inconclusive:{st_status}")

        # FIX 1: mutation floor (starve-proof) on every TLC-passing candidate.
        # Matrix: no site -> accept ("no_site"; the deterministic battery is
        # known low-recall, many good specs have no mutation site); kills but
        # ALL TypeOK-style -> REJECT "typeok_only_invariant" and iterate (the
        # spec's own safety invariant catches nothing semantic -- S4 gaming
        # surface, the model writes its own cfg); sites-but-no-kills -> accept
        # ("no_kill", weak signal, recorded); real safety catch -> accept
        # ("safety_catch"). S3 note: mutation_evidence disambiguates
        # safety_catch_rate null (no site) from 0.0 (sites, zero catches).
        mut = run_mutation_on_module(tla_path, cfg_text, mod, timeout)
        safety_catch_rate = mut.get("safety_catch_rate")
        attempted = mut.get("attempted") or 0
        killed = mut.get("killed") or 0
        safety_killed = mut.get("safety_killed") or 0
        if attempted == 0:
            mutation_evidence = "no_site"
        elif killed > 0 and safety_killed == 0:
            last_reason = "typeok_only_invariant"
            violated = sorted({m2.get("violated") for m2 in mut.get("mutants", [])
                               if m2.get("killed") and m2.get("violated")})
            error_context = _evidence(None, None, None, None,
                                       note="Mutation testing injected semantic faults "
                                            "into your spec and your invariant "
                                            f"{violated or ['(TypeOK-style)']} never "
                                            "caught them as a safety violation -- every "
                                            "catch was a TypeOK-style type check. Your "
                                            "invariant never catches semantic mutations; "
                                            "strengthen the safety property so it "
                                            "constrains real behavior, not just types.")
            continue
        elif killed == 0:
            mutation_evidence = "no_kill"
        else:
            mutation_evidence = "safety_catch"

        features = structural_features(mod_text)
        cscore = complexity_score(features)
        reward_weight = round(cscore * (1 + (safety_catch_rate or 0.0)), 3)

        return {
            "survived": True, "iters": it, "spec_text": mod_text, "cfg_text": cfg_text,
            "module": mod, "distinct_states": distinct_states, "vacuity": vac,
            "safety_catch_rate": safety_catch_rate, "kill_rate": mut.get("kill_rate"),
            "mutants_attempted": mut.get("attempted"),
            "mutation_evidence": mutation_evidence,
            "property_invariant": pi, "liveness_checked": liveness_checked,
            "liveness_property": liveness_property, "stutter_check": stutter_check,
            "features": features, "complexity_score": cscore,
            "reward_weight": reward_weight, "rejection_reason": None,
        }

    return {
        "survived": False, "iters": max_iters, "spec_text": None, "cfg_text": None,
        "module": module_name_, "distinct_states": None, "vacuity": None,
        "safety_catch_rate": None, "kill_rate": None, "mutants_attempted": None,
        "mutation_evidence": None, "property_invariant": None, "liveness_checked": None,
        "features": None, "complexity_score": None, "reward_weight": None,
        "rejection_reason": last_reason,
    }


# --------------------------------------------------------------- decontam

def decontam_survivor(spec_text: str, canon: dict):
    """Jaccard-vs-canonical decontam gate for a survivor (design: >= 0.65 vs
    the 206-corpus + tlaplus/examples + holdout-30 -- holdout-30 is a subset
    of the bench corpus, per project memory, so load_canonical's bench sweep
    already covers it). Returns (verdict, score)."""
    q = shingle_set(normalize_tla(spec_text), SHINGLE_K)
    _, score = nearest_similarity(q, canon)
    verdict = "rejected_contaminated" if score >= NEAR_DUP_THRESHOLD else "clean"
    return verdict, score


# --------------------------------------------------------------- driver

def _seed_key(source: str, k: int) -> str:
    return f"{source}::k{k}"


def run_w2(model, seeds_path: Path, raw: Path, run_dir: Path, seed_cap: int | None,
           k: int, timeout: int, max_iters: int, canon: dict | None = None):
    """Resumable driver: run_dir/w2_attempts.jsonl (every attempt, survived or
    not) + run_dir/w2_survivors.jsonl (decontam-clean survivors only). Skips
    seed x k keys already present in the attempts ledger so a restart resumes.
    Prints the yield rate (survivors / attempts) prominently."""
    from .w21_funnel import load_canonical

    run_dir = Path(run_dir)
    run_dir.mkdir(parents=True, exist_ok=True)
    seeds = [json.loads(l) for l in open(seeds_path) if l.strip()]
    if seed_cap:
        seeds = seeds[:seed_cap]

    attempts_path = run_dir / "w2_attempts.jsonl"
    survivors_path = run_dir / "w2_survivors.jsonl"
    done = set()
    if attempts_path.exists():
        done = {json.loads(l)["seed_key"] for l in open(attempts_path)}

    if canon is None:
        canon = load_canonical()

    n_attempts_this_run = 0
    n_survivors_this_run = 0

    with open(attempts_path, "a") as af, open(survivors_path, "a") as sf:
        for seed in seeds:
            source = seed["source"]
            for ki in range(k):
                key = _seed_key(source, ki)
                if key in done:
                    continue

                rel = source.removeprefix("data/raw/")
                spec_path = raw / rel
                spec_text = spec_path.read_text(errors="replace")
                cfg_candidates = list(spec_path.parent.glob("*.cfg"))
                cfg_path = next((c for c in cfg_candidates if c.stem == seed.get("module")), None) \
                    or (cfg_candidates[0] if cfg_candidates else None)
                cfg_text = cfg_path.read_text(errors="replace") if cfg_path else ""

                [nl_reply] = model.generate(backtranslate_prompt(spec_text, cfg_text), 1, 0.8, 4096)
                try:
                    nl = parse_nl(nl_reply)
                except NLMissingProperty:
                    # FIX 3a: no SAFETY PROPERTY: anchor -> the fidelity
                    # contract can't bind; skip the seed, spend nothing more.
                    af.write(json.dumps({"seed_key": key, "source": source, "k": ki,
                                          "survived": False, "iters": 0,
                                          "rejection_reason": "nl_missing_property"}) + "\n")
                    af.flush()
                    n_attempts_this_run += 1
                    continue

                workdir = run_dir / "work" / f"{seed.get('module', 'seed')}_k{ki}"
                result = run_loop_for_seed(model, nl, seed.get("module", "Gen"), workdir,
                                            timeout=timeout, max_iters=max_iters)

                attempt_row = {"seed_key": key, "source": source, "k": ki, "nl": nl,
                                **{k2: v for k2, v in result.items() if k2 != "spec_text"}}

                if result["survived"]:
                    verdict, score = decontam_survivor(result["spec_text"], canon)
                    attempt_row["decontam_verdict"] = verdict
                    attempt_row["decontam_similarity"] = score
                    if verdict == "clean":
                        sf.write(json.dumps({**result, "seed_key": key, "source": source,
                                              "k": ki, "nl": nl,
                                              "decontam_verdict": verdict,
                                              "decontam_similarity": score}) + "\n")
                        sf.flush()
                        n_survivors_this_run += 1
                    else:
                        attempt_row["survived"] = False
                        attempt_row["rejection_reason"] = "contaminated"

                af.write(json.dumps(attempt_row) + "\n")
                af.flush()
                n_attempts_this_run += 1

    total_attempts = sum(1 for _ in open(attempts_path))
    total_survivors = sum(1 for _ in open(survivors_path))
    rate = (total_survivors / total_attempts) if total_attempts else 0.0
    print(f"W2 loop: {n_attempts_this_run} attempts this run, {n_survivors_this_run} survivors this run")
    print(f"YIELD RATE (survivors/attempts, cumulative): {total_survivors}/{total_attempts} = {rate:.3f}")


def w2_yield_report(run_dirs) -> dict:
    """Extra-2: one honest cumulative yield across MULTIPLE run dirs (smoke
    runs diverge into separate dirs; per-dir yields are not comparable).
    Returns {"attempts", "survivors", "yield_rate", "per_dir"} and prints."""
    per_dir = {}
    attempts = survivors = 0
    for d in run_dirs:
        d = Path(d)
        a_file, s_file = d / "w2_attempts.jsonl", d / "w2_survivors.jsonl"
        a = sum(1 for _ in open(a_file)) if a_file.exists() else 0
        s = sum(1 for _ in open(s_file)) if s_file.exists() else 0
        per_dir[str(d)] = {"attempts": a, "survivors": s}
        attempts += a
        survivors += s
    rate = (survivors / attempts) if attempts else 0.0
    for name, st in per_dir.items():
        print(f"  {name}: {st['survivors']}/{st['attempts']}")
    print(f"CUMULATIVE YIELD RATE: {survivors}/{attempts} = {rate:.3f}")
    return {"attempts": attempts, "survivors": survivors, "yield_rate": rate,
            "per_dir": per_dir}


# --------------------------------------------------------------- dry-run model

class DryRunModel:
    """Canned fake model for --dry-run: exercises the whole pipeline (real
    SANY/TLC/mutation/decontam gates) with zero API spend. Alternates a
    plausible NL back-translation reply with a small, always-valid generated
    module+cfg so the loop converges on iter 1 for any seed."""
    id = "dry-run-canned-v1"

    _NL = ("A bounded resource counter. A single integer variable tracks how "
           "many units are currently allocated, starting at zero. Two actions "
           "are possible at each step: allocate one more unit, or release one "
           "unit, but release is only permitted while the count is already at "
           "least one greater than zero so the count never goes negative.\n\n"
           "SAFETY PROPERTY: the allocated count is always non-negative "
           "(greater than or equal to zero).")

    _MODULE = """---- MODULE {mod} ----
EXTENDS Integers
VARIABLE cnt
Init == cnt = 0
Alloc == cnt < 3 /\\ cnt' = cnt + 1
Release == cnt > 0 /\\ cnt' = cnt - 1
Next == Alloc \\/ Release
Spec == Init /\\ [][Next]_cnt
NonNegative == cnt >= 0
====
"""
    _CFG = "INIT Init\nNEXT Next\nINVARIANT NonNegative\n"

    def generate(self, prompt, n, temperature, max_tokens):
        if "NATURAL LANGUAGE DESCRIPTION" in prompt:
            mmod = re.search(r"Name the module `(\w+)`", prompt)
            mod = mmod.group(1) if mmod else "Gen"
            reply = (f"```tla\n{self._MODULE.format(mod=mod)}\n```\n"
                     f"```cfg\n{self._CFG}\n```\n"
                     "PROPERTY_INVARIANT: NonNegative\n")
        else:
            reply = f"Natural language description:\n\n```\n{self._NL}\n```\n"
        return [reply] * n


def main():
    ap = argparse.ArgumentParser(prog="harness.w2_loop")
    ap.add_argument("--seeds", type=Path,
                    default=Path("/Users/eric/GitHub/prove-TLA/data/chattla-corpora-v2/manifest_w2_seeds.jsonl"))
    ap.add_argument("--raw", type=Path,
                    default=Path("/Users/eric/GitHub/tla-dataset-pipeline/data/raw"))
    ap.add_argument("--run-dir", type=Path)
    ap.add_argument("--report-dirs", nargs="+", type=Path,
                    help="aggregate w2_attempts/w2_survivors across these run "
                         "dirs and print one cumulative yield rate, then exit")
    ap.add_argument("--seed-cap", type=int, default=500)
    ap.add_argument("--k", type=int, default=1)
    ap.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT_S)
    ap.add_argument("--max-iters", type=int, default=DEFAULT_MAX_ITERS)
    ap.add_argument("--model", default=None,
                    help="anthropic|anthropic:<id>|openai:<id>|stub (harness.repair.make_model)")
    ap.add_argument("--dry-run", action="store_true",
                    help="use the built-in canned DryRunModel, zero API spend")
    a = ap.parse_args()

    if a.report_dirs:
        w2_yield_report(a.report_dirs)
        return
    if a.run_dir is None:
        ap.error("--run-dir is required unless --report-dirs is given")

    if a.dry_run:
        model = DryRunModel()
    else:
        if not a.model:
            raise SystemExit("--model is required unless --dry-run is given")
        from .repair import make_model
        model = make_model(a.model)

    run_w2(model, a.seeds, a.raw, a.run_dir, seed_cap=a.seed_cap, k=a.k,
           timeout=a.timeout, max_iters=a.max_iters)


if __name__ == "__main__":
    main()
