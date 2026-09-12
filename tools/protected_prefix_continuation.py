#!/usr/bin/env python3
"""Base/parent/child continuation from a supplied canonical reference prefix.

This is a causal completion diagnostic. Most output bytes are supplied from a
verified reference, so even a valid assembled module is never model or gate
credit. The model generates only the suffix beginning at ``Next ==``.
"""
import argparse
import hashlib
import importlib.metadata
import json
from pathlib import Path
import site
import sys
import time

try:
    import protected_checkpoint_preflight as preflight
    import protected_checkpoint_paired_generation as paired
    import protected_reference_eos_replay as replay
    from protected_greedy_grammar_selector import GreedyGrammarSelector
except ModuleNotFoundError:
    from tools import protected_checkpoint_preflight as preflight
    from tools import protected_checkpoint_paired_generation as paired
    from tools import protected_reference_eos_replay as replay
    from tools.protected_greedy_grammar_selector import GreedyGrammarSelector

PHASES = ("base", "parent", "child")
ROWS = (47, 107)
PROMPT_TOKENS = {47: 401, 107: 457}
PREFIX = {
    47: ("85691e1dd47493d3be2afd894e781bdaf6b77d3a8d43e9cae4fa26b8c0edbd5d", 182, 226),
    107: ("2c70fbec2364b35a803dffb1b17b40b58abbc0c7ce34569cf015dbc6e9eb5326", 488, 673),
}
MAX_NEW_TOKENS = 256
AUDIT_STEPS = 4
SEED = 20261011
PARENT_SHA = "fba2768ed9a8f629f6496dc1ef72763b32fc339c74ba9075d1ffc53acd6c2d1d"
CHILD_SHA = "b0399b51aed001051fe200751b3087fc008482ca9dfeb64eb12884f71eee3bb6"


def plan():
    return [(phase, row) for phase in PHASES for row in ROWS]


def file_sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_new(path, value):
    with path.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(value, indent=2) + "\n")


def conditioned_inputs(tokenizer, prompt, frozen_encoding, prefix_text):
    """Append exact supplied bytes after the frozen assistant-generation header."""
    rendered = tokenizer.apply_chat_template(
        [{"role": "user", "content": prompt}], tokenize=False,
        add_generation_prompt=True)
    base = tokenizer(rendered, return_tensors="pt", add_special_tokens=False)
    actual = base["input_ids"][0].tolist()
    expected = frozen_encoding["input_ids"][:frozen_encoding["prompt_tokens"]]
    if actual != expected:
        raise ValueError("unconditioned generation input differs from frozen packet")
    conditioned_text = rendered + prefix_text
    inputs = tokenizer(conditioned_text, return_tensors="pt", add_special_tokens=False)
    ids = inputs["input_ids"][0].tolist()
    if ids[:len(expected)] != expected or not conditioned_text.endswith(prefix_text):
        raise ValueError("supplied prefix changed the frozen user-chat token prefix")
    return inputs, ids


def prepare_references(tokenizer, xgrammar, compiled, corpus):
    refs = {r["row"]: r["text"] for r in corpus["references"] if r.get("row") in ROWS}
    if set(refs) != set(ROWS):
        raise ValueError("protected canonical references missing")
    prepared = {}
    eos = tokenizer.eos_token_id
    if not isinstance(eos, int):
        raise ValueError("single EOS token required")
    for row in ROWS:
        text = refs[row]
        ids, prefix_ids, prefix_text, split = replay.split_reference(tokenizer, text)
        expected_sha, expected_prefix_tokens, expected_reference_tokens = PREFIX[row]
        if (paired.sha(prefix_text) != expected_sha or len(prefix_ids) != expected_prefix_tokens
                or len(ids) != expected_reference_tokens):
            raise ValueError("frozen supplied-prefix identity differs")
        matcher = xgrammar.GrammarMatcher(compiled)
        if not all(matcher.accept_token(token) for token in ids):
            raise ValueError("complete canonical reference rejected")
        if not matcher.is_completed() or not matcher.accept_token(eos) or not matcher.is_terminated():
            raise ValueError("reference completion/EOS preflight failed")
        prefix_matcher = xgrammar.GrammarMatcher(compiled)
        if not all(prefix_matcher.accept_token(token) for token in prefix_ids):
            raise ValueError("supplied canonical prefix rejected")
        if not prefix_matcher.accept_token(ids[split]):
            raise ValueError("first withheld reference token rejected")
        prepared[row] = dict(text=text, ids=ids, prefix_text=prefix_text,
            prefix_ids=prefix_ids, reference_suffix=text[len(prefix_text):],
            reference_suffix_ids=ids[split:])
    return prepared


def load_states(torch, parent, child, model_files):
    states, configs = {}, {}
    for phase, path in (("parent", parent), ("child", child)):
        saved = torch.load(path, map_location="cpu", weights_only=True)
        config = saved.get("config", {})
        if config.get("model_files") != model_files or config.get("dtype_profile") != preflight.PROFILE:
            raise ValueError(f"{phase} checkpoint base model/dtype profile mismatch")
        if phase == "child" and config.get("parent_sha256") != PARENT_SHA:
            raise ValueError("child checkpoint parent lineage mismatch")
        states[phase] = {"trainable_state": saved.get("trainable_state")}
        configs[phase] = {key: config[key] for key in
            ("dtype_profile", "model_files", "parent_sha256", "parent_checkpoint_sha256",
             "kind", "schema") if key in config}
    return states, configs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("packet", "corpus", "grammar", "model", "parent", "child",
                 "xgrammar-site", "output"):
        parser.add_argument("--" + name, type=Path, required=name != "output")
    parser.add_argument("--preflight-only", action="store_true")
    args = parser.parse_args()
    if not args.preflight_only and args.output is None:
        raise ValueError("output required for generation")
    if args.output is not None and args.output.exists():
        raise ValueError("append-only output already exists")
    for path, expected, label in (
        (args.packet, preflight.PACKET_SHA, "packet"),
        (args.corpus, replay.CORPUS_SHA, "corpus"),
        (args.grammar, replay.GRAMMAR_SHA, "grammar"),
        (args.parent, PARENT_SHA, "parent"),
        (args.child, CHILD_SHA, "child"),
    ):
        if file_sha(path) != expected:
            raise ValueError(f"frozen {label} hash mismatch")
    site.addsitedir(str(args.xgrammar_site))
    import xgrammar
    import torch
    import transformers
    if importlib.metadata.version("xgrammar") != "0.2.2":
        raise ValueError("exact xgrammar 0.2.2 required")
    packet = json.loads(args.packet.read_text())
    selected_rows = preflight.protected_rows(packet)
    model_files = preflight.model_files(args.model)
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    prompt_evidence = preflight.verify_prompt_tokens(tokenizer, selected_rows)
    info = xgrammar.TokenizerInfo.from_huggingface(tokenizer, vocab_size=tokenizer.vocab_size)
    compiled = xgrammar.GrammarCompiler(info, max_threads=1).compile_grammar(args.grammar.read_text())
    refs = prepare_references(tokenizer, xgrammar, compiled, json.loads(args.corpus.read_text()))
    for row in ROWS:
        source, encoding = selected_rows[row]
        if prompt_evidence[str(row)]["prompt_tokens"] != PROMPT_TOKENS[row]:
            raise ValueError("frozen user prompt token count differs")
        conditioned_inputs(tokenizer, source["prompt"], encoding, refs[row]["prefix_text"])
    states, configs = load_states(torch, args.parent, args.child, model_files)
    if args.preflight_only:
        print(json.dumps(dict(kind="protected_prefix_continuation_preflight_v1",
            complete=True, rows=list(ROWS), phases=list(PHASES),
            prefix_tokens={str(row): len(refs[row]["prefix_ids"]) for row in ROWS},
            reference_tokens={str(row): len(refs[row]["ids"]) for row in ROWS},
            xgrammar_version="0.2.2", checkpoint_loader="weights_only=True",
            model_weights_loaded=False, cuda_touched=False, gate_claim=False), sort_keys=True))
        return
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("CUDA bf16 required")
    model = transformers.AutoModelForCausalLM.from_pretrained(
        args.model, local_files_only=True, torch_dtype=torch.bfloat16,
        attn_implementation="sdpa").to("cuda").eval().requires_grad_(False)
    layer = model.model.layers[-1]
    layer.to(dtype=torch.float32)
    layer_ids = {id(parameter) for parameter in layer.parameters()}
    selected = {name: parameter for name, parameter in model.named_parameters()
                if id(parameter) in layer_ids}
    if len(selected) != 9 or len(layer_ids) != 9:
        raise ValueError("expected exactly 9 final-layer tensors")
    states["base"] = {"trainable_state": {
        name: parameter.detach().cpu().clone() for name, parameter in selected.items()}}
    for phase in PHASES:
        state = states[phase]["trainable_state"]
        if not isinstance(state, dict) or set(state) != set(selected):
            raise ValueError(f"{phase} trainable tensor names mismatch")
        for name, parameter in selected.items():
            value = state[name]
            if (value.dtype != torch.float32 or value.dtype != parameter.dtype
                    or value.shape != parameter.shape or not torch.isfinite(value).all()):
                raise ValueError(f"{phase} tensor mismatch: {name}")
    base_kwargs = dict(max_new_tokens=MAX_NEW_TOKENS, do_sample=False,
                       pad_token_id=tokenizer.eos_token_id)
    paired.validate_greedy_configuration(model, base_kwargs)
    args.output.mkdir(parents=True, exist_ok=False)
    records, phase_weights = [], {}
    started = time.monotonic()
    with torch.inference_mode():
        for phase in PHASES:
            if phase != "base":
                preflight.restore_exact(selected, states[phase])
            state = states[phase]["trainable_state"]
            if not all(torch.equal(parameter.detach().cpu(), state[name])
                       for name, parameter in selected.items()):
                raise ValueError(f"{phase} actual final-layer weights differ")
            identity = dict(phase=phase, model_files=model_files, dtype_profile=preflight.PROFILE,
                checkpoint_sha256={"base": None, "parent": PARENT_SHA, "child": CHILD_SHA}[phase],
                checkpoint_config=configs.get(phase), final_layer_tensor_count=9,
                restored_parameter_count=0 if phase == "base" else 9,
                restored_tensors_exact=phase != "base", actual_tensors_exact=True,
                final_layer_sha256={name: paired.sha(value.contiguous().numpy().tobytes())
                                    for name, value in state.items()})
            phase_weights[phase] = identity
            write_new(args.output / f"weights-{phase}.json", identity)
            for row in ROWS:
                source, encoding = selected_rows[row]
                ref = refs[row]
                inputs, conditioned_ids = conditioned_inputs(
                    tokenizer, source["prompt"], encoding, ref["prefix_text"])
                inputs = inputs.to("cuda")
                selector = GreedyGrammarSelector(xgrammar, compiled, audit_steps=AUDIT_STEPS)
                if not all(selector.matcher.accept_token(token) for token in ref["prefix_ids"]):
                    raise ValueError("actual selector rejected supplied prefix")
                seed = SEED + row * 10
                torch.manual_seed(seed)
                kwargs = dict(base_kwargs, logits_processor=[selector])
                resolved = paired.validate_greedy_configuration(model, kwargs)
                torch.cuda.synchronize()
                generation_started = time.monotonic()
                with torch.autocast(device_type="cuda", dtype=torch.bfloat16):
                    generated = model.generate(**inputs, **kwargs)
                torch.cuda.synchronize()
                seconds = time.monotonic() - generation_started
                full_ids = generated[0].tolist()
                if full_ids[:len(conditioned_ids)] != conditioned_ids:
                    raise ValueError("generated sequence changed conditioned input")
                continuation_ids = full_ids[len(conditioned_ids):]
                if not continuation_ids or len(continuation_ids) > MAX_NEW_TOKENS:
                    raise ValueError("continuation outside frozen budget")
                selector.validate_generated(continuation_ids)
                continuation = tokenizer.decode(continuation_ids, skip_special_tokens=True)
                raw = ref["prefix_text"] + continuation
                eos_ended = continuation_ids[-1] == tokenizer.eos_token_id
                grammar_completed = selector.matcher.is_terminated()
                record = dict(phase=phase, row=row, generation_seed=seed,
                    base_prompt_sha256=paired.sha(source["prompt"]),
                    actual_user_prompt_tokens_match_frozen=True,
                    actual_user_prompt_token_count=PROMPT_TOKENS[row],
                    conditioned_input_token_ids=conditioned_ids,
                    supplied_prefix_sha256=paired.sha(ref["prefix_text"]),
                    supplied_prefix_tokens=len(ref["prefix_ids"]),
                    reference_tokens=len(ref["ids"]),
                    supplied_fraction=len(ref["prefix_ids"])/len(ref["ids"]),
                    reference_suffix_sha256=paired.sha(ref["reference_suffix"]),
                    reference_suffix_tokens=len(ref["reference_suffix_ids"]),
                    continuation=continuation, continuation_sha256=paired.sha(continuation),
                    continuation_token_ids=continuation_ids,
                    continuation_token_count=len(continuation_ids),
                    continuation_matches_reference_suffix=(continuation == ref["reference_suffix"]),
                    raw_reply=raw, raw_reply_sha256=paired.sha(raw),
                    eos_ended=eos_ended, grammar_completed=grammar_completed,
                    finish_reason="eos" if eos_ended else "token_limit" if len(continuation_ids)==MAX_NEW_TOKENS else "other_stop",
                    resolved_decode=resolved, wall_seconds=seconds, weights_identity=identity,
                    selector_evidence=dict(method="ranked_greedy_primed_canonical_prefix",
                        full_mask_audits=selector.audit_count,
                        candidates_checked=selector.candidates_checked,
                        actual_generated_ids_match=True),
                    grammar_enforced=True, reference_conditioning=True, training=False,
                    supplied_reference_credit=False, producer="direct_prefix_continuation")
                write_new(args.output / f"row-{row}-{phase}.json", record)
                records.append(record)
                print(json.dumps(dict(phase=phase,row=row,
                    continuation_tokens=len(continuation_ids),eos_ended=eos_ended,
                    grammar_completed=grammar_completed)),flush=True)
    if [(record["phase"],record["row"]) for record in records] != plan():
        raise ValueError("incomplete or reordered plan")
    receipt = dict(kind="protected_prefix_continuation_v1",complete=True,
        contract=dict(phases=list(PHASES),rows=list(ROWS),ordered_plan=[dict(phase=p,row=r) for p,r in plan()],
            max_new_tokens=MAX_NEW_TOKENS,audit_steps=AUDIT_STEPS,seed=SEED,
            grammar_enforced=True,reference_conditioning=True,training=False,
            supplied_reference_credit=False),packet_sha256=preflight.PACKET_SHA,
        corpus_sha256=replay.CORPUS_SHA,grammar_sha256=replay.GRAMMAR_SHA,
        parent_checkpoint_sha256=PARENT_SHA,child_checkpoint_sha256=CHILD_SHA,
        model_files=model_files,protected_prompt_tokens=prompt_evidence,
        phase_weights=phase_weights,records=records,wall_seconds=time.monotonic()-started,
        provenance=dict(producer="direct_prefix_continuation",interpreter=sys.executable,
            torch=torch.__version__,transformers=transformers.__version__,xgrammar="0.2.2",
            cuda_device=torch.cuda.get_device_name(),dtype_profile=preflight.PROFILE,
            source_sha256={Path(path).name:file_sha(path) for path in
                (__file__,preflight.__file__,paired.__file__,replay.__file__,
                 sys.modules[GreedyGrammarSelector.__module__].__file__)}),
        scope="Two TRAIN-row supplied-reference-prefix diagnostic; no model/gate credit",
        producer="direct_prefix_continuation",gate_claim=False,model_improvement_claim=False)
    write_new(args.output / "receipt.json", receipt)


if __name__ == "__main__":
    main()
