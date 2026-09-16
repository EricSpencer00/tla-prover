#!/usr/bin/env python3
"""Prefix-preserving grammar repair with traced bounded layout-aware rollback.

The repair arm is deliberately different from whole-response grammar masking:
the ordinary greedy response is retained byte-for-byte through its longest
grammar-accepted token prefix.  Only the suffix after the first rejected token
is regenerated.  This is a diagnostic, not a quality or gate claim: all output
bytes remain subject to independent SANY scoring and protected rows are never
used for training.

The repair uses the audited layout-aware selector as the last logits processor,
so Transformers retains its KV cache while the selector performs an exact
finite-vocabulary ranked search with stable ties, early dense audits, and a
conservative indentation guard. If a guarded suffix reaches a finite-token
dead end, v7 retries only a bounded set of rollback windows, banning the exact
token chosen at each rollback point. There is no post-hoc byte edit or
grammar-only fallback; exhausting the windows fails closed.
Only the suffix after the first rejected token is regenerated, under an
explicit repair-token budget. CPU preflight exercises the selector protocol on
a tiny grammar and never loads model weights or touches CUDA.
"""

import argparse
from dataclasses import dataclass
import hashlib
import importlib.metadata
import json
from pathlib import Path
import site
import time

try:
    import protected_checkpoint_preflight as preflight
except ModuleNotFoundError:
    from tools import protected_checkpoint_preflight as preflight
try:
    from layout_junction_audit import line_guard
except ModuleNotFoundError:
    from tools.layout_junction_audit import line_guard
try:
    from precedence_guard import precedence_guard
except ModuleNotFoundError:
    from tools.precedence_guard_audit import precedence_guard
try:
    from comment_guard import comment_guard
except ModuleNotFoundError:
    from tools.comment_guard import comment_guard


PACKET_SHA = "a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c"
CORPUS_SHA = "fb76468f6a3217a359d54da92a2e3fa25396aad0547e6b5eb35129193a0e812a"
GRAMMAR_SHA = "2bcc86946f0a858628f455a3d0648c7117e2b780743e1f25dff82cebd0fb4d67"
CHILD_SHA = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"
ROWS = (47, 107)
MAX_NEW_TOKENS = 2048
REPAIR_MAX_NEW_TOKENS = 512
SELECTOR_AUDIT_STEPS = 4
BACKTRACK_WINDOWS = (64, 128, 256, 512)
SEED = 20260916


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_new(path, value):
    with Path(path).open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(value, indent=2) + "\n")


def exact_inputs(args):
    expected = ((args.packet, PACKET_SHA, "packet"),
                (args.corpus, CORPUS_SHA, "corpus"),
                (args.grammar, GRAMMAR_SHA, "grammar"),
                (args.checkpoint, CHILD_SHA, "child"))
    for path, wanted, label in expected:
        if sha(path) != wanted:
            raise ValueError(f"frozen {label} hash mismatch")
    if args.output.exists():
        raise ValueError("append-only output already exists")


def load_tokenizer(args):
    from transformers import AutoTokenizer
    return AutoTokenizer.from_pretrained(args.model, local_files_only=True)


def load_selector():
    try:
        from layout_aware_greedy_grammar_selector import (
            LayoutAwareGreedyGrammarSelector, LayoutGuardDeadEnd)
    except ModuleNotFoundError:
        from tools.layout_aware_greedy_grammar_selector import (
            LayoutAwareGreedyGrammarSelector, LayoutGuardDeadEnd)
    return LayoutAwareGreedyGrammarSelector, LayoutGuardDeadEnd


class BoundedBacktrackingFailure(ValueError):
    """A guarded suffix failed after all declared rollback attempts."""

    def __init__(self, *, row_prefix, rejected_at, baseline_response_tokens,
                 attempts, selected_tokens, windows):
        super().__init__("bounded guard backtracking exhausted without a finite continuation")
        self.row_prefix = tuple(int(token) for token in row_prefix)
        self.rejected_at = int(rejected_at)
        self.baseline_response_tokens = int(baseline_response_tokens)
        self.attempts = list(attempts)
        self.selected_tokens = int(selected_tokens)
        self.windows = tuple(int(window) for window in windows)


def compile_grammar(args, tokenizer):
    site.addsitedir(str(args.xgrammar_site))
    import xgrammar
    if importlib.metadata.version("xgrammar") != "0.2.2":
        raise ValueError("exact xgrammar 0.2.2 required")
    config = json.loads((args.model / "config.json").read_text())
    vocab_size = config.get("vocab_size")
    eos = tokenizer.eos_token_id
    if type(vocab_size) is not int or vocab_size <= 0:
        raise ValueError("positive model-config vocabulary required")
    if not isinstance(eos, int) or not 0 <= eos < vocab_size:
        raise ValueError("EOS outside model-config vocabulary")
    if len(tokenizer) > vocab_size or tokenizer.vocab_size > vocab_size:
        raise ValueError("tokenizer vocabulary exceeds model-config vocabulary")
    info = xgrammar.TokenizerInfo.from_huggingface(tokenizer, vocab_size=vocab_size)
    compiled = xgrammar.GrammarCompiler(info, max_threads=1).compile_grammar(
        args.grammar.read_text())
    return xgrammar, compiled, vocab_size


def protected_references(args, tokenizer, xgrammar, compiled):
    corpus = json.loads(args.corpus.read_text())
    refs = {item["row"]: item["text"] for item in corpus.get("references", [])
            if item.get("row") in ROWS}
    if set(refs) != set(ROWS):
        raise ValueError("both protected references required for CPU completeness guard")
    out = {}
    eos = tokenizer.eos_token_id
    for row in ROWS:
        ids = tokenizer.encode(refs[row], add_special_tokens=False)
        matcher = xgrammar.GrammarMatcher(compiled)
        if not all(matcher.accept_token(token) for token in ids):
            raise ValueError(f"protected reference row {row} rejected by repair grammar")
        if not matcher.is_completed() or not matcher.accept_token(eos) or not matcher.is_terminated():
            raise ValueError(f"protected reference row {row} fails grammar/EOS completion")
        out[row] = dict(reference_tokens=len(ids), reference_sha256=hashlib.sha256(
            refs[row].encode()).hexdigest())
    return out


def prime(xgrammar, compiled, token_ids):
    matcher = xgrammar.GrammarMatcher(compiled)
    for token in token_ids:
        if not matcher.accept_token(int(token)):
            return None
    return matcher


def longest_accepted_prefix(xgrammar, compiled, token_ids, tokenizer):
    matcher = xgrammar.GrammarMatcher(compiled)
    accepted = []
    response_text = ""
    for index, token in enumerate(token_ids):
        piece = tokenizer.decode([int(token)], skip_special_tokens=False,
                                 clean_up_tokenization_spaces=False)
        candidate = response_text + piece
        if (line_guard(candidate) or precedence_guard(candidate) or
                comment_guard(candidate)):
            return accepted, index, False, matcher.is_terminated()
        if not matcher.accept_token(int(token)):
            return accepted, index, False, matcher.is_terminated()
        accepted.append(int(token))
        response_text += piece
        if matcher.is_terminated():
            return accepted, index + 1, True, True
    return accepted, len(accepted), False, matcher.is_terminated()


@dataclass(frozen=True)
class Beam:
    token_ids: tuple
    score: float
    ended: bool


def top_accepted(xgrammar, compiled, prefix, scores, branch_k):
    """Return exact finite-score accepted continuations, stable by token ID."""
    ranked = sorted(range(len(scores)), key=lambda token: (-float(scores[token]), token))
    found = []
    for token in ranked:
        value = float(scores[token])
        if value == float("-inf"):
            break
        matcher = prime(xgrammar, compiled, prefix)
        if matcher is None:
            raise ValueError("beam prefix is not grammar accepted")
        if matcher.accept_token(token):
            found.append((token, value, matcher.is_terminated()))
            if len(found) == branch_k:
                break
    if not found:
        raise ValueError("no finite grammar-accepted beam continuation")
    return found


def synthetic_ranked_control(xgrammar):
    """Exercise prefix priming, exact ranked selection, rollback, and EOS."""
    import torch
    GreedyGrammarSelector, _ = load_selector()
    class FakeTokenizer:
        def decode(self, ids, **kwargs):
            return "".join({0: "", 1: "a", 2: "b", 3: "", 4: "x", 5: "<eos>"}[int(i)] for i in ids)
    tokenizer = FakeTokenizer()
    info = xgrammar.TokenizerInfo(["ax", "a", "b", "ab", "x", "<eos>"], stop_token_ids=[5])
    compiled = xgrammar.GrammarCompiler(info, max_threads=1).compile_grammar(
        'root ::= "ab"')
    selector = GreedyGrammarSelector(xgrammar, compiled, tokenizer, audit_steps=3)
    if not selector.matcher.accept_token(1):
        raise ValueError("first-rejection prefix control failed")
    inputs = torch.tensor([[4, 4]])
    scores = torch.tensor([[10., 9., 8., 7., 6., 11.]])
    actual = int(selector(inputs, scores).argmax())
    if actual != 2:
        raise ValueError("ranked selector chose the wrong legal token")
    inputs = torch.cat([inputs, torch.tensor([[actual]])], dim=1)
    actual = int(selector(inputs, scores).argmax())
    if actual != 5:
        raise ValueError("ranked selector did not commit EOS")
    selector.validate_generated([2, 5])
    if not selector.matcher.is_terminated() or selector.audit_count != 2:
        raise ValueError("EOS termination control failed")
    rejected_prefix, reject_at, ended, _ = longest_accepted_prefix(
        xgrammar, compiled, [1, 5], tokenizer)
    if rejected_prefix != [1] or reject_at != 1 or ended:
        raise ValueError("baseline first-rejection control failed")
    return dict(prefix_priming=True, exact_ranked_selection=True,
                stable_ties=True, eos_termination=True, first_rejection=True,
                torch_imported=True)


def synthetic_bounded_backtrack_control(xgrammar):
    """Exercise a rollback ban without model weights or CUDA."""
    import torch
    GreedyGrammarSelector, DeadEnd = load_selector()

    class FakeTokenizer:
        def decode(self, ids, **kwargs):
            return "".join({0: "", 1: "a", 2: "b", 3: "", 4: "x", 5: "<eos>"}[int(i)] for i in ids)

    tokenizer = FakeTokenizer()
    info = xgrammar.TokenizerInfo(["ax", "a", "b", "ab", "x", "<eos>"], stop_token_ids=[5])
    compiled = xgrammar.GrammarCompiler(info, max_threads=1).compile_grammar(
        'root ::= "ab" | "ax"')
    selector = GreedyGrammarSelector(
        xgrammar, compiled, tokenizer, audit_steps=0,
        banned_token_ids_by_step={0: {2}})
    if not selector.matcher.accept_token(1):
        raise ValueError("backtrack prefix control failed")
    inputs = torch.tensor([[4, 4]])
    scores = torch.tensor([[10., 9., 12., 7., 11., 1.]])
    actual = int(selector(inputs, scores).argmax())
    if actual != 4:
        raise ValueError("rollback ban did not choose the finite alternate")
    inputs = torch.cat([inputs, torch.tensor([[actual]])], dim=1)
    actual = int(selector(inputs, torch.tensor([[10., 9., 8., 7., 6., 12.]] )).argmax())
    if actual != 5:
        raise ValueError("rollback alternate did not terminate")
    selector.validate_generated([4, 5])
    if not selector.matcher.is_terminated():
        raise ValueError("rollback alternate failed EOS termination")
    return dict(rollback_ban=True, finite_alternate=True,
                eos_termination=True, dead_end_type=DeadEnd.__name__)


def synthetic_failure_trace_control():
    """Require every bounded attempt to have an auditable failure record."""
    sample = [
        dict(attempt=0, status="dead_end", rollback_tokens=None,
             banned_token=None, remaining_tokens=512, selected_tokens=512,
             failure_steps=512),
        dict(attempt=1, status="dead_end", rollback_tokens=448,
             banned_token=17, remaining_tokens=64, selected_tokens=64,
             failure_steps=64),
    ]
    required = ("attempt", "status", "rollback_tokens", "banned_token",
                "remaining_tokens", "selected_tokens", "failure_steps")
    if any(set(required) - set(item) for item in sample):
        raise ValueError("failure trace fields are incomplete")
    if [item["attempt"] for item in sample] != [0, 1]:
        raise ValueError("failure trace attempt ordering is unstable")
    return dict(partial_failure_receipt=True, required_fields=list(required),
                ordered_attempts=True, no_sany_or_quality_credit=True)


def synthetic_comment_free_control(references):
    """Scope comment-free repair to the two comment-free protected references."""
    if sorted(references) != list(ROWS):
        raise ValueError("comment-free control requires both protected references")
    if any(comment_guard(references[row]) for row in ROWS):
        raise ValueError("protected reference unexpectedly contains a comment")
    sample = "---- MODULE CommentControl ----\\nA == TRUE\\n\\* generated comment\\n===="
    if not comment_guard(sample):
        raise ValueError("comment guard failed its positive control")
    return dict(protected_reference_comment_free=True,
                protected_reference_denominator=len(ROWS),
                synthetic_comment_rejection=True,
                universal_false_reject_audit=False)


def frozen_inputs(tokenizer, source, encoding):
    rendered = tokenizer.apply_chat_template(
        [{"role": "user", "content": source["prompt"]}],
        tokenize=False, add_generation_prompt=True)
    inputs = tokenizer(rendered, return_tensors="pt", add_special_tokens=False)
    actual = inputs["input_ids"][0].tolist()
    expected = encoding["input_ids"][:encoding["prompt_tokens"]]
    if actual != expected:
        raise ValueError("frozen prompt token IDs changed")
    return inputs, rendered


def load_child(torch, args, model_files):
    saved = torch.load(args.checkpoint, map_location="cpu", weights_only=True)
    config = saved.get("config", {})
    if config.get("model_files") != model_files:
        raise ValueError("checkpoint model-file identity mismatch")
    if config.get("dtype_profile") != preflight.PROFILE:
        raise ValueError("checkpoint dtype profile mismatch")
    return saved


def run_repair(model, tokenizer, xgrammar, compiled, prompt_inputs, baseline_ids,
               *, repair_max_new_tokens, selector_audit_steps, pad_id,
               backtrack_windows):
    import torch
    GreedyGrammarSelector, DeadEnd = load_selector()
    response = baseline_ids[len(prompt_inputs["input_ids"][0]):]
    prefix, rejected_at, baseline_grammar_ended, _ = longest_accepted_prefix(
        xgrammar, compiled, response, tokenizer)
    if baseline_grammar_ended:
        return dict(prefix=prefix, rejected_at=rejected_at, repaired=[],
                    output=prefix, selector_audits=0, grammar_ended=True,
                    repair_steps=0, baseline_response_tokens=len(response),
                    backtrack_attempts=[], backtrack_windows=list(backtrack_windows))
    prompt_ids = prompt_inputs["input_ids"]

    def attempt(seed_tokens, banned_token_ids_by_step, max_new_tokens):
        selector = GreedyGrammarSelector(
            xgrammar, compiled, tokenizer,
            audit_steps=selector_audit_steps,
            response_text=tokenizer.decode(prefix + seed_tokens,
                                            skip_special_tokens=False,
                                            clean_up_tokenization_spaces=False),
            banned_token_ids_by_step=banned_token_ids_by_step)
        accepted = prefix + seed_tokens
        if not all(selector.matcher.accept_token(token) for token in accepted):
            raise ValueError("accepted rollback prefix could not prime selector")
        prefix_tensor = torch.tensor([accepted], device=prompt_ids.device,
                                     dtype=prompt_ids.dtype)
        conditioned_ids = torch.cat([prompt_ids, prefix_tensor], dim=1)
        conditioned_mask = torch.ones_like(conditioned_ids)
        started = time.monotonic()
        with torch.inference_mode():
            with torch.autocast(device_type="cuda", dtype=torch.bfloat16):
                generated = model.generate(
                    input_ids=conditioned_ids, attention_mask=conditioned_mask,
                    max_new_tokens=max_new_tokens, do_sample=False,
                    pad_token_id=pad_id, logits_processor=[selector])
        repaired = generated[0].tolist()[conditioned_ids.shape[1]:]
        selector.validate_generated(repaired)
        output = accepted + repaired
        matcher = prime(xgrammar, compiled, output)
        if matcher is None:
            raise ValueError("ranked repair failed final grammar replay")
        return dict(prefix=prefix, rejected_at=rejected_at,
                    seed_tokens=seed_tokens,
                    repaired=list(seed_tokens) + list(repaired),
                    output=output, selector_audits=selector.audit_count,
                    grammar_ended=matcher.is_terminated(),
                    repair_steps=len(seed_tokens) + len(repaired),
                    baseline_response_tokens=len(response),
                    repair_wall_seconds=time.monotonic() - started)

    attempts = []
    try:
        result = attempt([], {}, repair_max_new_tokens)
        result["backtrack_attempts"] = attempts
        result["backtrack_windows"] = list(backtrack_windows)
        return result
    except DeadEnd as failure:
        latest = list(failure.selected_token_ids)
        attempts.append(dict(attempt=0, status="dead_end", rollback_tokens=None,
                             banned_token=None, remaining_tokens=repair_max_new_tokens,
                             selected_tokens=len(latest), failure_steps=failure.steps))

    for attempt_number, window in enumerate(backtrack_windows, start=1):
        if not isinstance(window, int) or window <= 0:
            raise ValueError("backtrack windows must be positive integers")
        if not latest:
            break
        rollback = max(0, len(latest) - window)
        if rollback >= len(latest):
            continue
        remaining = repair_max_new_tokens - rollback
        if remaining <= 0:
            continue
        seed = latest[:rollback]
        banned_token = int(latest[rollback])
        banned = {0: {banned_token}}
        try:
            result = attempt(seed, banned, remaining)
            attempts.append(dict(attempt=attempt_number, status="terminated",
                                 rollback_tokens=rollback,
                                 banned_token=banned_token,
                                 remaining_tokens=remaining,
                                 selected_tokens=len(seed), failure_steps=None))
            result["backtrack_attempts"] = attempts
            result["backtrack_windows"] = list(backtrack_windows)
            return result
        except DeadEnd as failure:
            latest = list(failure.selected_token_ids)
            attempts.append(dict(attempt=attempt_number, status="dead_end",
                                 rollback_tokens=rollback,
                                 banned_token=banned_token,
                                 remaining_tokens=remaining,
                                 selected_tokens=len(latest), failure_steps=failure.steps))
    raise BoundedBacktrackingFailure(
        row_prefix=prefix, rejected_at=rejected_at,
        baseline_response_tokens=len(response), attempts=attempts,
        selected_tokens=len(latest), windows=backtrack_windows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("packet", "corpus", "grammar", "model", "checkpoint", "xgrammar-site"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--preflight-only", action="store_true")
    parser.add_argument("--max-new-tokens", type=int, default=MAX_NEW_TOKENS)
    parser.add_argument("--repair-max-new-tokens", type=int, default=REPAIR_MAX_NEW_TOKENS)
    parser.add_argument("--selector-audit-steps", type=int, default=SELECTOR_AUDIT_STEPS)
    parser.add_argument("--backtrack-windows", type=int, nargs="+",
                        default=list(BACKTRACK_WINDOWS))
    args = parser.parse_args()
    if (args.max_new_tokens <= 0 or args.repair_max_new_tokens <= 0 or
            args.selector_audit_steps < 0 or
            not args.backtrack_windows or
            any(isinstance(value, bool) or value <= 0 for value in args.backtrack_windows) or
            args.backtrack_windows != sorted(set(args.backtrack_windows))):
        raise ValueError("positive bounded search parameters required")
    exact_inputs(args)
    tokenizer = load_tokenizer(args)
    xgrammar, compiled, vocab_size = compile_grammar(args, tokenizer)
    packet = json.loads(args.packet.read_text())
    selected_rows = preflight.protected_rows(packet)
    prompt_evidence = preflight.verify_prompt_tokens(tokenizer, selected_rows)
    references = protected_references(args, tokenizer, xgrammar, compiled)
    corpus = json.loads(args.corpus.read_text())
    reference_texts = {item["row"]: item["text"] for item in corpus.get("references", [])
                       if item.get("row") in ROWS}
    comment_controls = synthetic_comment_free_control(reference_texts)
    controls = synthetic_ranked_control(xgrammar)
    backtrack_controls = synthetic_bounded_backtrack_control(xgrammar)
    failure_trace_controls = synthetic_failure_trace_control()
    if args.preflight_only:
        print(json.dumps(dict(kind="protected_layout_aware_repair_preflight_v1", complete=True,
            packet_sha256=PACKET_SHA, corpus_sha256=CORPUS_SHA, grammar_sha256=GRAMMAR_SHA,
            child_checkpoint_sha256=CHILD_SHA, rows=list(ROWS), protected_references=references,
            protected_prompt_tokens=prompt_evidence,
            synthetic_controls=controls,
            bounded_backtracking_controls=backtrack_controls,
            failure_trace_controls=failure_trace_controls,
            comment_free_repair_controls=comment_controls,
            xgrammar_version="0.2.2", vocabulary_size=vocab_size,
            max_new_tokens=args.max_new_tokens, repair_max_new_tokens=args.repair_max_new_tokens,
            selector_audit_steps=args.selector_audit_steps,
            backtrack_windows=args.backtrack_windows,
            model_weights_loaded=False, cuda_touched=False, gate_claim=False,
            model_improvement_claim=False), sort_keys=True))
        return

    import torch
    import transformers
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("CUDA bf16 required")
    packet = json.loads(args.packet.read_text())
    selected = preflight.protected_rows(packet)
    prompt_evidence = preflight.verify_prompt_tokens(tokenizer, selected)
    model_files = preflight.model_files(args.model)
    saved = load_child(torch, args, model_files)
    model = transformers.AutoModelForCausalLM.from_pretrained(
        args.model, local_files_only=True, torch_dtype=torch.bfloat16,
        attn_implementation="sdpa").to("cuda").eval().requires_grad_(False)
    last_layer = model.model.layers[-1]
    last_layer.to(dtype=torch.float32)
    selected_params = {name: parameter for name, parameter in model.named_parameters()
                       if id(parameter) in {id(p) for p in last_layer.parameters()}}
    preflight.restore_exact(selected_params, saved)
    args.output.mkdir(parents=False, exist_ok=False)
    records = []
    for row in ROWS:
        source, encoding = selected[row]
        prompt_inputs, _ = frozen_inputs(tokenizer, source, encoding)
        prompt_inputs = prompt_inputs.to("cuda")
        with torch.inference_mode():
            with torch.autocast(device_type="cuda", dtype=torch.bfloat16):
                baseline = model.generate(
                    **prompt_inputs, max_new_tokens=args.max_new_tokens, do_sample=False,
                    pad_token_id=tokenizer.eos_token_id)
        try:
            repaired = run_repair(model, tokenizer, xgrammar, compiled, prompt_inputs,
                                  baseline[0].tolist(),
                                  repair_max_new_tokens=args.repair_max_new_tokens,
                                  selector_audit_steps=args.selector_audit_steps,
                                  pad_id=tokenizer.eos_token_id,
                                  backtrack_windows=args.backtrack_windows)
        except BoundedBacktrackingFailure as failure:
            baseline_reply = tokenizer.decode(
                baseline[0].tolist()[prompt_inputs["input_ids"].shape[1]:],
                skip_special_tokens=True)
            failure_record = dict(
                kind="protected_layout_aware_repair_failure_v1",
                complete=False, row=row, generation_seed=SEED + row,
                prompt_tokens=int(prompt_inputs["input_ids"].shape[1]),
                prompt_tokens_match_frozen=True,
                baseline_reply_sha256=hashlib.sha256(baseline_reply.encode()).hexdigest(),
                baseline_response_tokens=failure.baseline_response_tokens,
                accepted_prefix_tokens=len(failure.row_prefix),
                first_rejected_response_token=failure.rejected_at,
                repair_max_new_tokens=args.repair_max_new_tokens,
                selector_audit_steps=args.selector_audit_steps,
                backtrack_windows=list(failure.windows),
                selected_tokens_at_failure=failure.selected_tokens,
                backtrack_attempts=failure.attempts,
                failure=str(failure),
                protected_reference_conditioning=False, training=False,
                supplied_reference_credit=False, gate_claim=False,
                model_improvement_claim=False,
            )
            write_new(args.output / f"failure-row-{row}.json", failure_record)
            print(json.dumps(dict(event="failure", row=row,
                                  failure=str(failure),
                                  attempts=len(failure.attempts))), flush=True)
            raise
        baseline_reply = tokenizer.decode(
            baseline[0].tolist()[prompt_inputs["input_ids"].shape[1]:], skip_special_tokens=True)
        repaired_reply = tokenizer.decode(repaired["output"], skip_special_tokens=True)
        record = dict(row=row, generation_seed=SEED + row,
            prompt_tokens=int(prompt_inputs["input_ids"].shape[1]),
            prompt_tokens_match_frozen=True, baseline_reply=baseline_reply,
            baseline_reply_sha256=hashlib.sha256(baseline_reply.encode()).hexdigest(),
            baseline_response_tokens=repaired["baseline_response_tokens"],
            accepted_prefix_tokens=len(repaired["prefix"]),
            first_rejected_response_token=repaired["rejected_at"],
            repaired_reply=repaired_reply,
            repaired_reply_sha256=hashlib.sha256(repaired_reply.encode()).hexdigest(),
            repaired_response_tokens=len(repaired["output"]),
            repair_tokens=len(repaired["repaired"]),
            grammar_ended=repaired["grammar_ended"],
            repair_max_new_tokens=args.repair_max_new_tokens,
            selector_audit_steps=args.selector_audit_steps,
            backtrack_windows=args.backtrack_windows,
            repair_wall_seconds=repaired.get("repair_wall_seconds"),
            backtrack_attempts=repaired["backtrack_attempts"],
            protected_reference_conditioning=False, training=False,
            supplied_reference_credit=False, gate_claim=False,
            model_improvement_claim=False)
        write_new(args.output / f"row-{row}.json", record)
        records.append(record)
        print(json.dumps(dict(event="row", row=row,
                              accepted_prefix_tokens=record["accepted_prefix_tokens"],
                              repair_tokens=record["repair_tokens"],
                              grammar_ended=record["grammar_ended"])), flush=True)
    receipt = dict(kind="protected_layout_aware_repair_v6", complete=len(records) == len(ROWS),
        contract=dict(rows=list(ROWS), max_new_tokens=args.max_new_tokens,
                      repair_max_new_tokens=args.repair_max_new_tokens,
                      selector_audit_steps=args.selector_audit_steps,
                      backtrack_windows=args.backtrack_windows,
                      failure_trace_fields=["attempt", "status", "rollback_tokens",
                                            "banned_token", "remaining_tokens",
                                            "selected_tokens", "failure_steps"],
                      prefix_preserving=True, reference_conditioning=False,
                      training=False, supplied_reference_credit=False),
        packet_sha256=PACKET_SHA, corpus_sha256=CORPUS_SHA, grammar_sha256=GRAMMAR_SHA,
        child_checkpoint_sha256=CHILD_SHA, model_files=model_files,
        restored_tensors_exact=True, protected_prompt_tokens=prompt_evidence,
        xgrammar_version=importlib.metadata.version("xgrammar"), records=records,
        producer="protected_prefix_preserving_layout_aware_repair",
        gate_claim=False, model_improvement_claim=False)
    write_new(args.output / "receipt.json", receipt)


if __name__ == "__main__":
    main()
