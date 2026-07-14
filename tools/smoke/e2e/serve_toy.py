"""Stage D of the toy e2e smoke: an OpenAI-compatible /v1/chat/completions
server that mirrors the two vLLM behaviors the harness depends on:

  1. normal generation (from the merged toy model, --model-dir), and
  2. the context-length 400 error (--max-model-len): if prompt_tokens +
     max_tokens exceeds the limit, return HTTP 400 exactly like vLLM did in
     the quarantined Gate-2 framing-B run. gate-check must catch this.

--canned-corpus <corpus_data_dir> mode: instead of sampling the toy model
(which cannot write TLA+), answer every request with the CANONICAL spec for
the module named in the prompt, so gen-eval's full pass-path (extraction ->
SANY -> TLC -> verdict "pass") is exercised deterministically.

Usage:
  .venv/bin/python serve_toy.py --port 8399 --model-dir <merged_toy> \
      [--canned-corpus /path/to/corpus/data] [--max-model-len 32768]
"""
import argparse
import json
import re
import time
from pathlib import Path

import uvicorn
from fastapi import FastAPI, Request
from fastapi.responses import JSONResponse

app = FastAPI()
STATE: dict = {}


def _count_tokens(text: str) -> int:
    tok = STATE.get("tok")
    if tok is not None:
        return len(tok(text)["input_ids"])
    return max(1, len(text) // 4)


def _canned_reply(prompt: str) -> str:
    """Find the module the prompt asks for and return its canonical spec.
    gen-eval framing-A prompts contain 'MODULE <name>'; we map name->spec
    file by scanning the corpus tla_files dir once."""
    idx = STATE["canned_index"]
    m = re.search(r"MODULE\s+(\w+)", prompt)
    if m and m.group(1) in idx:
        return (f"Here is the module:\n\n```tla\n"
                f"{Path(idx[m.group(1)]).read_text(errors='replace')}\n```\n")
    for name, path in idx.items():
        if re.search(rf"\b{re.escape(name)}\b", prompt):
            return f"Here is the module:\n\n```tla\n{Path(path).read_text(errors='replace')}\n```\n"
    # fall back: first spec (still a real module; likely scores fail, not error)
    any_path = next(iter(idx.values()))
    return f"```tla\n{Path(any_path).read_text(errors='replace')}\n```\n"


@app.get("/v1/models")
def models():
    return {"object": "list", "data": [{"id": STATE["model_id"], "object": "model"}]}


@app.post("/v1/chat/completions")
async def chat(request: Request):
    body = await request.json()
    prompt = "\n".join(m.get("content", "") for m in body.get("messages", []))
    max_tokens = int(body.get("max_tokens", 1024))
    n_prompt = _count_tokens(prompt)

    limit = STATE["max_model_len"]
    if n_prompt + max_tokens > limit:
        # vLLM-style context-length 400 (the exact failure class that
        # invalidated Gate-2 framing B on 2026-07-14)
        return JSONResponse(status_code=400, content={"error": {
            "message": (f"This model's maximum context length is {limit} tokens. "
                        f"However, you requested {n_prompt + max_tokens} tokens "
                        f"({n_prompt} in the messages, {max_tokens} in the completion)."),
            "type": "BadRequestError", "code": 400}})

    if STATE.get("canned_index"):
        text = _canned_reply(prompt)
    else:
        tok, model = STATE["tok"], STATE["model"]
        ids = tok(prompt[-2000:], return_tensors="pt", truncation=True, max_length=512)
        gen = model.generate(**ids, max_new_tokens=min(max_tokens, 64),
                             do_sample=True, temperature=max(body.get("temperature", 0.8), 0.1),
                             pad_token_id=tok.eos_token_id)
        text = tok.decode(gen[0][ids["input_ids"].shape[1]:], skip_special_tokens=True)

    n_out = _count_tokens(text)
    return {"id": "cmpl-smoke", "object": "chat.completion", "created": int(time.time()),
            "model": STATE["model_id"],
            "choices": [{"index": 0, "finish_reason": "stop",
                         "message": {"role": "assistant", "content": text}}],
            "usage": {"prompt_tokens": n_prompt, "completion_tokens": n_out,
                      "total_tokens": n_prompt + n_out}}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", type=int, default=8399)
    ap.add_argument("--model-dir", default=None)
    ap.add_argument("--canned-corpus", default=None,
                    help="corpus data dir; answer with canonical specs (pass-path test)")
    ap.add_argument("--max-model-len", type=int, default=32768)
    a = ap.parse_args()

    STATE["max_model_len"] = a.max_model_len
    STATE["model_id"] = "toy"
    if a.model_dir:
        from transformers import AutoModelForCausalLM, AutoTokenizer
        STATE["tok"] = AutoTokenizer.from_pretrained(a.model_dir)
        STATE["model"] = AutoModelForCausalLM.from_pretrained(a.model_dir)
    if a.canned_corpus:
        tla_dir = Path(a.canned_corpus) / "tla_files"
        index = {}
        for p in sorted(tla_dir.glob("*.tla")):
            m = re.search(r"MODULE\s+(\w+)", p.read_text(errors="replace"))
            if m:
                index[m.group(1)] = str(p)
        STATE["canned_index"] = index
        print(f"canned mode: {len(index)} modules indexed from {tla_dir}")

    uvicorn.run(app, host="127.0.0.1", port=a.port, log_level="warning")


if __name__ == "__main__":
    main()
