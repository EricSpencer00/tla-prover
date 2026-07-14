"""Stage C of the toy e2e smoke: a REAL SFT train (LoRA) on the harmony jsonl
produced by stage B, followed by a REAL merge, on a tiny model so it runs in
minutes on CPU. This is a mechanics test of the train->merge leg (data format,
tokenization, loss goes down, merged weights load and generate), not a
capability test.

Usage: .venv/bin/python train_toy.py --sft <sft_smoke.jsonl> --out <dir>
"""
import argparse
import json
from pathlib import Path

import torch
from datasets import Dataset
from peft import LoraConfig, get_peft_model
from transformers import (AutoModelForCausalLM, AutoTokenizer, Trainer,
                          TrainingArguments)

MODEL_ID = "HuggingFaceTB/SmolLM2-135M"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sft", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--steps", type=int, default=15)
    a = ap.parse_args()
    out = Path(a.out)

    texts = [json.loads(l)["text"] for l in open(a.sft) if l.strip()]
    assert texts, "empty SFT file"
    # tiny corpus: repeat so the trainer has enough rows for --steps
    texts = (texts * ((4 * a.steps) // len(texts) + 1))[: 4 * a.steps]

    tok = AutoTokenizer.from_pretrained(MODEL_ID)
    tok.pad_token = tok.pad_token or tok.eos_token
    model = AutoModelForCausalLM.from_pretrained(MODEL_ID, torch_dtype=torch.float32)
    model = get_peft_model(model, LoraConfig(r=8, lora_alpha=16, task_type="CAUSAL_LM"))

    def tokenize(batch):
        enc = tok(batch["text"], truncation=True, max_length=512, padding="max_length")
        enc["labels"] = [ids.copy() for ids in enc["input_ids"]]
        return enc

    ds = Dataset.from_dict({"text": texts}).map(tokenize, batched=True,
                                                remove_columns=["text"])
    trainer = Trainer(
        model=model,
        train_dataset=ds,
        args=TrainingArguments(output_dir=str(out / "trainer"), max_steps=a.steps,
                               per_device_train_batch_size=4, learning_rate=2e-4,
                               logging_steps=1, report_to=[], save_strategy="no",
                               use_cpu=not torch.backends.mps.is_available()),
    )
    trainer.train()
    losses = [h["loss"] for h in trainer.state.log_history if "loss" in h]
    print(f"loss first={losses[0]:.3f} last={losses[-1]:.3f}")
    assert losses[-1] < losses[0], "loss did not decrease -- training leg broken"

    merged = model.merge_and_unload()
    merged_dir = out / "merged_toy"
    merged.save_pretrained(merged_dir)
    tok.save_pretrained(merged_dir)

    # reload-and-generate proves the merged artifact is self-contained
    m2 = AutoModelForCausalLM.from_pretrained(merged_dir)
    t2 = AutoTokenizer.from_pretrained(merged_dir)
    ids = t2("---- MODULE", return_tensors="pt")
    gen = m2.generate(**ids, max_new_tokens=8, do_sample=False,
                      pad_token_id=t2.eos_token_id)
    print("merged model generates:", t2.decode(gen[0])[:80].replace("\n", " "))
    print(f"TRAIN+MERGE: OK -> {merged_dir}")


if __name__ == "__main__":
    main()
