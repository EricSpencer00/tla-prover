#!/usr/bin/env python3
"""Offline tiny-model pipeline pilot; never a 120B quality evaluation.

Run with tools/smoke/e2e/.venv/bin/python tools/local_sany_pilot.py.
The supervisor bounds loading, generation and verification together.
"""
import argparse
import hashlib
import inspect
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import uuid
from unittest.mock import patch

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))
MODEL_ID = "Qwen/Qwen2.5-0.5B-Instruct"


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def worker(args):
    os.environ["TLA_LOOP_EXTRACTION_FEEDBACK"] = "1" if args.extraction_feedback else "0"
    # Both the Hub and Transformers must refuse network resolution.
    os.environ.update(HF_HUB_OFFLINE="1", TRANSFORMERS_OFFLINE="1",
                      HF_HUB_DISABLE_TELEMETRY="1", TOKENIZERS_PARALLELISM="false")
    import torch
    import transformers
    from transformers import AutoModelForCausalLM, AutoTokenizer
    from harness import loop_eval
    from harness.decoding import effective_params_sha256
    from harness.gen_eval import DEFAULT_CORPUS
    from harness.repair import Model

    rundir = REPO / "results/runs" / args.run_id
    cache = Path.home() / ".cache/huggingface/hub/models--Qwen--Qwen2.5-0.5B-Instruct"
    snapshots = sorted((cache / "snapshots").glob("*"))
    snapshots = [p for p in snapshots if (p / "model.safetensors").is_file()]
    if not snapshots:
        raise FileNotFoundError(f"No cached weights in {cache}; downloads forbidden")
    snapshot = snapshots[-1]
    torch.set_num_threads(4)
    device = "mps" if torch.backends.mps.is_available() else "cpu"
    tokenizer = AutoTokenizer.from_pretrained(snapshot, local_files_only=True,
                                              trust_remote_code=False)
    net = AutoModelForCausalLM.from_pretrained(
        snapshot, local_files_only=True, trust_remote_code=False,
        torch_dtype=torch.float32).to(device).eval()
    backend = {"model": MODEL_ID, "snapshot": snapshot.name, "device": device,
               "dtype": "float32", "torch": torch.__version__,
               "transformers": transformers.__version__, "threads": 4}
    backend_hash = effective_params_sha256(backend)
    write_json(rundir / "backend.json", backend)

    class LocalQwen(Model):
        id = MODEL_ID + "@" + snapshot.name + ":offline-pilot"

        def generate_traced(self, prompt, n, temperature, max_tokens, seed=None):
            assert n == 1, "pilot is sequential"
            torch.manual_seed(seed or 0)
            rendered = tokenizer.apply_chat_template(
                [{"role": "user", "content": prompt}], tokenize=False,
                add_generation_prompt=True)
            inputs = tokenizer(rendered, return_tensors="pt").to(device)
            params = {"max_new_tokens": min(max_tokens, 512),
                      "do_sample": temperature > 0, "top_p": 1.0,
                      "top_k": 0, "repetition_penalty": 1.0,
                      "pad_token_id": tokenizer.eos_token_id}
            if temperature > 0:
                params["temperature"] = temperature
            started = time.monotonic()
            with torch.inference_mode():
                output = net.generate(**inputs, **params)
            tokens = output[0, inputs.input_ids.shape[1]:]
            reply = tokenizer.decode(tokens, skip_special_tokens=True)
            trace = {"prompt": prompt, "rendered_prompt": rendered,
                     "prompt_sha256": hashlib.sha256(prompt.encode()).hexdigest(),
                     "reply": reply, "output_token_ids": tokens.tolist(),
                     "output_tokens": len(tokens), "input_tokens": inputs.input_ids.shape[1],
                     "generation_s": round(time.monotonic() - started, 3),
                     "hit_token_limit": len(tokens) == params["max_new_tokens"],
                     "seed": seed, "params": params}
            with (rundir / "generations.jsonl").open("a") as fh:
                fh.write(json.dumps(trace) + "\n")
            print(f"generated {len(tokens)} tokens in {trace['generation_s']}s", flush=True)
            return [(reply, {"decode_seed": seed, "seed_supported": True,
                             "provider_seed_echo": None,
                             "decode_params_sha256": effective_params_sha256(params),
                             "backend_sha256": backend_hash})]

        def generate(self, *a, **kw):
            return [text for text, _ in self.generate_traced(*a, **kw)]

    model = LocalQwen()
    kwargs = dict(corpus=DEFAULT_CORPUS, run_id=args.run_id, model_name=model.id,
                  chains=1, rounds=2, specs=["2", "5"], resume=False)
    supports_model = "model" in inspect.signature(loop_eval.run_loop_eval).parameters
    write_json(rundir / "injection.json", {"model_parameter": supports_model,
               "method": "model parameter" if supports_model else "scoped make_model factory",
               "scorer_unchanged": True})
    # Only generation budget/model injection changes; scorer and gates stay intact.
    with patch.object(loop_eval, "MAX_TOKENS", 512):
        if supports_model:
            loop_eval.run_loop_eval(**kwargs, model=model)
        else:
            with patch.object(loop_eval, "make_model", return_value=model):
                loop_eval.run_loop_eval(**kwargs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=int, default=180, choices=range(1, 181),
                        metavar="SECONDS")
    parser.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--extraction-feedback", action="store_true",
                        help="Enable experimental extraction feedback (default off)")
    parser.add_argument("--run-id", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.worker:
        worker(args)
        return 0
    args.run_id = "local-sany-pilot-" + time.strftime("%Y%m%d-%H%M%S") + "-" + uuid.uuid4().hex[:8]
    rundir = REPO / "results/runs" / args.run_id
    rundir.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    print(f"Run: {rundir}", flush=True)
    with (rundir / "console.log").open("w") as log:
        proc = subprocess.Popen([sys.executable, "-u", str(Path(__file__).resolve()),
                                 "--worker", "--run-id", args.run_id] +
                                (["--extraction-feedback"] if args.extraction_feedback else []),
                                cwd=REPO, stdout=log, stderr=subprocess.STDOUT,
                                start_new_session=True)
        timed_out = False
        try:
            code = proc.wait(timeout=args.timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(proc.pid, signal.SIGKILL)
            code = proc.wait()
    rows_path = rundir / "rows.jsonl"
    rows = [json.loads(s) for s in rows_path.read_text().splitlines()] if rows_path.exists() else []
    report = {"run_id": args.run_id, "scope": "tiny-model pipeline pilot, not 120B quality",
              "extraction_feedback": args.extraction_feedback,
              "timeout_s": args.timeout, "elapsed_s": round(time.monotonic() - started, 2),
              "timed_out": timed_out, "exit_code": code, "rows": len(rows),
              "specs_observed": sorted({r["spec"] for r in rows}),
              "verdicts": [r.get("verdict") for r in rows],
              "complete": code == 0 and {r["spec"] for r in rows} == {"2", "5"}}
    write_json(rundir / "pilot.json", report)
    print(json.dumps(report, indent=2))
    return 0 if report["complete"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
