"""Build and run structured-span preference training using the verified trainer.

The trainer's optimizer/checkpoint/restore path is intentionally reused; this
wrapper changes only the preference-pair construction to complete structural
spans whose corrupted controls are SANY-screened.
"""
import argparse
import json
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
try:
    from tools.proof_syntax_preference_train import (
        BUDGET, PACKET_SHA, PARENT_SHA, TRAIN, VALID, PROTECTED, file_sha, sha,
        sany, train,
    )
    from tools.proof_syntax_structure_diagnostic import structural_spans
except ModuleNotFoundError:
    # The PBS stage is intentionally isolated; import sibling files when the
    # complete repository package is not present in the stage directory.
    import importlib.util
    _ROOT = Path(__file__).resolve().parent
    def _load(name):
        spec = importlib.util.spec_from_file_location(name, _ROOT / (name + '.py'))
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        return module
    _pref = _load('proof_syntax_preference_train')
    _diag = _load('proof_syntax_structure_diagnostic')
    BUDGET, PACKET_SHA, PARENT_SHA = _pref.BUDGET, _pref.PACKET_SHA, _pref.PARENT_SHA
    TRAIN, VALID, PROTECTED = _pref.TRAIN, _pref.VALID, _pref.PROTECTED
    file_sha, sha, sany, train = _pref.file_sha, _pref.sha, _pref.sany, _pref.train
    structural_spans = _diag.structural_spans


def build(args):
    packet = json.loads(args.packet.read_text())
    if sha(args.packet.read_bytes()) != PACKET_SHA:
        raise ValueError("frozen packet changed")
    args.output.mkdir(parents=True, exist_ok=False)
    pairs = []
    for row_index in TRAIN + VALID:
        row = packet["rows"][row_index]
        good = row["response"]
        positive = sany(good, args.output / f"controls/{row_index}/positive", args.java, args.jar)
        if positive["passed"] is not True:
            raise ValueError(f"positive SANY control failed for {row_index}")
        for index, span in enumerate(structural_spans(good)):
            start = good.find(span["text"])
            first = next(i for i, c in enumerate(span["text"]) if not c.isspace())
            bad = good[:start] + span["text"][:first] + "@" + span["text"][first + 1:] + good[start + len(span["text"]):]
            negative = sany(bad, args.output / f"controls/{row_index}/negative-{index}", args.java, args.jar)
            if negative["passed"] is not False:
                raise ValueError(f"corruption unexpectedly passed SANY: {row_index}/{index}")
            pairs.append(dict(row=row_index, id=row["id"],
                              split="train" if row_index in TRAIN else "validation",
                              kind=f"{span['kind']}_span", positive_sha256=sha(good.encode()),
                              span_text=span["text"], negative=bad,
                              negative_sha256=sha(bad.encode())))
    manifest = dict(kind="syntax_structured_span_preference_v1", packet_sha256=PACKET_SHA,
                    parent_checkpoint_sha256=PARENT_SHA, train_rows=list(TRAIN),
                    validation_rows=list(VALID), protected_rows=list(PROTECTED),
                    budget=dict(BUDGET, objective="multi_token_structural_span"),
                    sany_jar_sha256=file_sha(args.jar), pairs=pairs,
                    no_protected_training=True, gate_claim=False)
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({"pairs": len(pairs), "manifest_sha256": file_sha(args.output / "manifest.json")}))


def main():
    p = argparse.ArgumentParser()
    p.add_argument("mode", choices=("prepare", "train"))
    p.add_argument("--packet", type=Path, required=True)
    p.add_argument("--jar", type=Path, required=True)
    p.add_argument("--java", default="java")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--manifest", type=Path)
    p.add_argument("--manifest-sha256")
    p.add_argument("--checkpoint", type=Path)
    p.add_argument("--model", type=Path)
    a = p.parse_args()
    if a.mode == "prepare":
        build(a)
    else:
        if not all((a.manifest, a.manifest_sha256, a.checkpoint, a.model)):
            p.error("train requires manifest/hash/checkpoint/model")
        train(a)


if __name__ == "__main__":
    main()
