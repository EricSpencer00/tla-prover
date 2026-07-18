"""Serve preflight: run BEFORE every gen-eval launch against a live endpoint.
Would have caught the 2026-07-14 Gate-2 framing-B disaster (serve at
--max-model-len 4096 vs repair prompts of 4.4k-17k tokens) in ~10 seconds
instead of after a full quarantined run.

Probes, against OPENAI_BASE_URL (or --base-url):
  1. /v1/models reachable; served model name printed (mismatch = wrong server)
  2. short request returns 200 with non-empty content
  3. LONG request: ~18k-token prompt + max_tokens=16384 (the harness's actual
     framing-B worst case) must return 200 -- a 400 means the serve context
     window is too small for the eval about to be launched.

Usage:
  OPENAI_BASE_URL=http://localhost:8322/v1 python3 tools/smoke/serve_preflight.py \
      --model chattla-v2-120b [--max-tokens 16384] [--prompt-tokens 18000]
Exit 0 = safe to launch; nonzero = DO NOT launch the eval.
"""
import argparse
import json
import os
import sys
import urllib.error
import urllib.request


def _post(url, body, timeout=900):
    req = urllib.request.Request(
        url, data=json.dumps(body).encode(),
        headers={"Authorization": f"Bearer {os.environ.get('OPENAI_API_KEY', 'dummy')}",
                 "content-type": "application/json",
                 "User-Agent": "prove-tla-harness/1.0"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.loads(resp.read())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--base-url", default=os.environ.get("OPENAI_BASE_URL"))
    ap.add_argument("--model", required=True)
    ap.add_argument("--max-tokens", type=int, default=16384,
                    help="must match the harness budget (gen_eval MAX_TOKENS)")
    ap.add_argument("--prompt-tokens", type=int, default=18000,
                    help="approx worst-case prompt size (framing-B 17k + margin)")
    a = ap.parse_args()
    if not a.base_url:
        sys.exit("set OPENAI_BASE_URL or --base-url")
    base = a.base_url.rstrip("/")

    print(f"[1/3] GET {base}/models")
    with urllib.request.urlopen(urllib.request.Request(
            base + "/models", headers={"User-Agent": "prove-tla-harness/1.0"}),
            timeout=60) as r:
        ids = [m["id"] for m in json.loads(r.read()).get("data", [])]
    print(f"      served models: {ids}")
    if a.model not in ids:
        sys.exit(f"PREFLIGHT FAIL: model {a.model!r} not served (got {ids})")

    print("[2/3] short completion")
    d = _post(base + "/chat/completions",
              {"model": a.model, "max_tokens": 32,
               "messages": [{"role": "user", "content": "Say OK."}]})
    msg = (d.get("choices") or [{}])[0].get("message") or {}
    if not (msg.get("content") or msg.get("reasoning_content") or msg.get("reasoning")):
        sys.exit(f"PREFLIGHT FAIL: empty completion: {json.dumps(d)[:400]}")
    print("      ok")

    # ~4 chars/token heuristic; oversized is fine -- we WANT the worst case
    long_prompt = ("VARIABLE x " * (a.prompt_tokens // 2))[: a.prompt_tokens * 4]
    print(f"[3/3] long probe: ~{a.prompt_tokens} prompt tokens + max_tokens={a.max_tokens}")
    try:
        _post(base + "/chat/completions",
              {"model": a.model, "max_tokens": a.max_tokens, "temperature": 0.0,
               "messages": [{"role": "user", "content":
                             long_prompt + "\nReply with the single word OK."}]})
    except urllib.error.HTTPError as e:
        body = e.read().decode(errors="replace")[:400]
        sys.exit(f"PREFLIGHT FAIL: long request -> HTTP {e.code}. The serve "
                 f"context window cannot fit this eval's worst-case request; "
                 f"fix --max-model-len before launching.\n{body}")
    print("      ok")
    print("PREFLIGHT OK: safe to launch gen-eval")


if __name__ == "__main__":
    main()
