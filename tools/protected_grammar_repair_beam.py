#!/usr/bin/env python3
"""Prefix-preserving grammar repair with a bounded deterministic beam.

The repair arm is deliberately different from whole-response grammar masking:
the ordinary greedy response is retained byte-for-byte through its longest
grammar-accepted token prefix.  Only the suffix after the first rejected token
is regenerated.  This is a diagnostic, not a quality or gate claim: all output
bytes remain subject to independent SANY scoring and protected rows are never
used for training.

The beam is implemented explicitly rather than through ``generate(num_beams)``
so each candidate has an independently replayed XGrammar matcher.  Candidate
selection is exact over the finite vocabulary (no rank cutoff), stable on ties,
and bounded by ``beam_width``/``branch_k``.  CPU preflight exercises the same
state protocol on a tiny grammar and never loads model weights or touches CUDA.
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


PACKET_SHA = "a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c"
CORPUS_SHA = "fb76468f6a3217a359d54da92a2e3fa25396aad0547e6b5eb35129193a0e812a"
GRAMMAR_SHA = "2bcc86946f0a858628f455a3d0648c7117e2b780743e1f25dff82cebd0fb4d67"
CHILD_SHA = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"
ROWS = (47, 107)
MAX_NEW_TOKENS = 2048
BEAM_WIDTH = 2
BRANCH_K = 2
SEED = 20260915


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


def longest_accepted_prefix(xgrammar, compiled, token_ids):
    matcher = xgrammar.GrammarMatcher(compiled)
    accepted = []
    for index, token in enumerate(token_ids):
        if not matcher.accept_token(int(token)):
            return accepted, index, False, matcher.is_terminated()
        accepted.append(int(token))
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


def synthetic_beam_control(xgrammar):
    """Exercise first-rejection recovery and independent beam state."""
    import torch
    info = xgrammar.TokenizerInfo(["ax", "a", "b", "ab", "x", "<eos>"], stop_token_ids=[5])
    compiled = xgrammar.GrammarCompiler(info, max_threads=1).compile_grammar(
        'root ::= "ab"')
    rejected_prefix, reject_at, ended, _ = longest_accepted_prefix(
        xgrammar, compiled, [1, 5])
    if rejected_prefix != [1] or reject_at != 1 or ended:
        raise ValueError("first-rejection prefix control failed")
    scores = [10.0, 9.0, 8.0, 7.0, 6.0, 11.0]
    first = top_accepted(xgrammar, compiled, [1], scores, 2)
    if [token for token, _, _ in first] != [2]:
        raise ValueError("single legal branch control failed")
    # A fresh branch must not inherit the other branch's matcher state.
    branch_a = top_accepted(xgrammar, compiled, [], [10., 9., 8., 7., 6., 11.], 2)
    if [token for token, _, _ in branch_a] != [1, 2]:
        raise ValueError("stable branch ordering control failed")
    eos = prime(xgrammar, compiled, [1, 2])
    if eos is None or not eos.accept_token(5) or not eos.is_terminated():
        raise ValueError("EOS termination control failed")
    return dict(first_rejection=True, branch_state_isolated=True,
                stable_ties=True, eos_termination=True, torch_imported=True)


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
               *, max_new_tokens, beam_width, branch_k, pad_id):
    response = baseline_ids[len(prompt_inputs["input_ids"][0]):]
    prefix, rejected_at, baseline_grammar_ended, _ = longest_accepted_prefix(
        xgrammar, compiled, response)
    if baseline_grammar_ended:
        return dict(prefix=prefix, rejected_at=rejected_at, repaired=[],
                    output=prefix, beam_score=0.0, grammar_ended=True,
                    repair_steps=0, baseline_response_tokens=len(response))

    beams = [Beam(tuple(prefix), 0.0, False)]
    started = time.monotonic()
    for _ in range(max_new_tokens):
        active = [beam for beam in beams if not beam.ended]
        if not active:
            break
        prompt_ids = prompt_inputs["input_ids"][0].tolist()
        batch = torch.tensor([prompt_ids + list(beam.token_ids) for beam in active],
                             device=model.device, dtype=torch.long)
        with torch.autocast(device_type="cuda", dtype=torch.bfloat16):
            logits = model(input_ids=batch, use_cache=False).logits[:, -1, :]
        candidates = []
        for beam, row_scores in zip(active, logits):
            for token, value, ended in top_accepted(
                    xgrammar, compiled, beam.token_ids, row_scores.detach().float().cpu().tolist(), branch_k):
                candidates.append(Beam(beam.token_ids + (token,),
                                       beam.score + value, ended))
        if not candidates:
            break
        candidates.sort(key=lambda beam: (-beam.score, beam.token_ids))
        beams = candidates[:beam_width]
        if any(beam.ended for beam in beams):
            # Preserve completed candidates but continue expanding active
            # alternatives until the best completed candidate is selected.
            completed = [beam for beam in beams if beam.ended]
            if len(completed) == beam_width:
                break
    beams.sort(key=lambda beam: (-beam.score, beam.token_ids))
    best = beams[0]
    repaired = list(best.token_ids[len(prefix):])
    matcher = prime(xgrammar, compiled, best.token_ids)
    if matcher is None:
        raise ValueError("selected beam failed final grammar replay")
    grammar_ended = matcher.is_terminated()
    return dict(prefix=prefix, rejected_at=rejected_at, repaired=repaired,
                output=list(best.token_ids), beam_score=best.score,
                grammar_ended=grammar_ended, repair_steps=len(repaired),
                baseline_response_tokens=len(response),
                repair_wall_seconds=time.monotonic() - started)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("packet", "corpus", "grammar", "model", "checkpoint", "xgrammar-site"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--preflight-only", action="store_true")
    parser.add_argument("--max-new-tokens", type=int, default=MAX_NEW_TOKENS)
    parser.add_argument("--beam-width", type=int, default=BEAM_WIDTH)
    parser.add_argument("--branch-k", type=int, default=BRANCH_K)
    args = parser.parse_args()
    if args.max_new_tokens <= 0 or args.beam_width <= 0 or args.branch_k <= 0:
        raise ValueError("positive bounded search parameters required")
    exact_inputs(args)
    tokenizer = load_tokenizer(args)
    xgrammar, compiled, vocab_size = compile_grammar(args, tokenizer)
    references = protected_references(args, tokenizer, xgrammar, compiled)
    controls = synthetic_beam_control(xgrammar)
    if args.preflight_only:
        print(json.dumps(dict(kind="protected_grammar_repair_beam_preflight_v1", complete=True,
            packet_sha256=PACKET_SHA, corpus_sha256=CORPUS_SHA, grammar_sha256=GRAMMAR_SHA,
            child_checkpoint_sha256=CHILD_SHA, rows=list(ROWS), protected_references=references,
            synthetic_controls=controls, xgrammar_version="0.2.2", vocabulary_size=vocab_size,
            max_new_tokens=args.max_new_tokens, beam_width=args.beam_width, branch_k=args.branch_k,
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
        repaired = run_repair(model, tokenizer, xgrammar, compiled, prompt_inputs,
                              baseline[0].tolist(), max_new_tokens=args.max_new_tokens,
                              beam_width=args.beam_width, branch_k=args.branch_k,
                              pad_id=tokenizer.eos_token_id)
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
            beam_width=args.beam_width, branch_k=args.branch_k,
            repair_wall_seconds=repaired.get("repair_wall_seconds"),
            protected_reference_conditioning=False, training=False,
            supplied_reference_credit=False, gate_claim=False,
            model_improvement_claim=False)
        write_new(args.output / f"row-{row}.json", record)
        records.append(record)
        print(json.dumps(dict(event="row", row=row,
                              accepted_prefix_tokens=record["accepted_prefix_tokens"],
                              repair_tokens=record["repair_tokens"],
                              grammar_ended=record["grammar_ended"])), flush=True)
    receipt = dict(kind="protected_grammar_repair_beam_v1", complete=len(records) == len(ROWS),
        contract=dict(rows=list(ROWS), max_new_tokens=args.max_new_tokens,
                      beam_width=args.beam_width, branch_k=args.branch_k,
                      prefix_preserving=True, reference_conditioning=False,
                      training=False, supplied_reference_credit=False),
        packet_sha256=PACKET_SHA, corpus_sha256=CORPUS_SHA, grammar_sha256=GRAMMAR_SHA,
        child_checkpoint_sha256=CHILD_SHA, model_files=model_files,
        restored_tensors_exact=True, protected_prompt_tokens=prompt_evidence,
        xgrammar_version=importlib.metadata.version("xgrammar"), records=records,
        producer="protected_prefix_preserving_grammar_repair_beam",
        gate_claim=False, model_improvement_claim=False)
    write_new(args.output / "receipt.json", receipt)


if __name__ == "__main__":
    main()
