"""W3.1: lmgpa 119-theorem benchmark (arXiv:2512.09758, repo YUH-Z/lmgpa) as
the proof-side eval set for PLAN.md goal G2.

corpus/lmgpa/manifest.json (built by corpus/lmgpa/build_manifest.py) is the
frozen 119-entry index: {id, category, module_file, theorem_name, sha256}.
module_file is relative to the lmgpa checkout root (default sibling checkout
/Users/eric/GitHub/lmgpa, NOT copied into this repo).

Three subcommands:
  manifest  -- rebuild/print the manifest (delegates to build_manifest.build).
  decontam  -- Rule-4 near-dup check against the W2 survivor corpus and the
               206-spec tla_benchmark corpus; writes results/analysis/lmgpa_decontam.json.
  baseline  -- 0-model floor: run tlapm as-is (no model-authored proof) on every
               manifest module, resumable ledger at out_dir/rows.jsonl.

CLI: python3 -m harness.lmgpa_bench {manifest,decontam,baseline} ...
"""
import argparse
import json
from pathlib import Path

from .corpora import normalize_tla, shingle_set, nearest_similarity, NEAR_DUP_THRESHOLD
from .runner import REPO, check_tlapm

DEFAULT_LMGPA_ROOT = Path("/Users/eric/GitHub/lmgpa")
MANIFEST_PATH = REPO / "corpus" / "lmgpa" / "manifest.json"
DEFAULT_206_DIR = Path("/Users/eric/GitHub/tla_benchmark/data/tla_files")
DEFAULT_W2_SURVIVOR_GLOB = "results/runs/w2-gen*/w2_survivors.jsonl"


def load_manifest(path: Path = MANIFEST_PATH) -> list[dict]:
    return json.loads(path.read_text())


# ---------------------------------------------------------------------------
# decontam
# ---------------------------------------------------------------------------

def _load_w2_survivor_texts(repo: Path = REPO, pattern: str = DEFAULT_W2_SURVIVOR_GLOB) -> dict[str, str]:
    """{seed_key or synthetic-id: spec_text} across every w2_survivors.jsonl shard."""
    texts = {}
    for fp in sorted(repo.glob(pattern)):
        with fp.open() as fh:
            for i, line in enumerate(fh):
                line = line.strip()
                if not line:
                    continue
                row = json.loads(line)
                spec_text = row.get("spec_text")
                if not spec_text:
                    continue
                key = row.get("seed_key") or f"{fp.parent.name}:{i}"
                # de-dup identical keys across shards by suffixing shard name
                if key in texts:
                    key = f"{key}::{fp.parent.name}:{i}"
                texts[key] = spec_text
    return texts


def _load_206_texts(dir_path: Path = DEFAULT_206_DIR) -> dict[str, str]:
    texts = {}
    if not dir_path.exists():
        return texts
    for f in sorted(dir_path.glob("*.tla")):
        texts[f.stem] = f.read_text(errors="replace")
    return texts


def decontam_report(lmgpa_root: Path = DEFAULT_LMGPA_ROOT,
                     manifest: list[dict] | None = None,
                     w2_texts: dict[str, str] | None = None,
                     corpus206_texts: dict[str, str] | None = None,
                     out_path: Path | None = None) -> dict:
    """Nearest-similarity of each benchmark module against the W2 survivor
    corpus and the 206-spec corpus. Verdict 'clean' iff every theorem's max
    similarity against both canonical sets is < NEAR_DUP_THRESHOLD."""
    manifest = manifest if manifest is not None else load_manifest()
    w2_texts = w2_texts if w2_texts is not None else _load_w2_survivor_texts()
    corpus206_texts = corpus206_texts if corpus206_texts is not None else _load_206_texts()

    w2_shingles = {k: shingle_set(normalize_tla(t)) for k, t in w2_texts.items()}
    c206_shingles = {k: shingle_set(normalize_tla(t)) for k, t in corpus206_texts.items()}

    rows = []
    max_overall = 0.0
    for entry in manifest:
        mod_path = lmgpa_root / entry["module_file"]
        text = mod_path.read_text(errors="replace")
        q = shingle_set(normalize_tla(text))

        w2_name, w2_sim = nearest_similarity(q, w2_shingles) if w2_shingles else ("", 0.0)
        c206_name, c206_sim = nearest_similarity(q, c206_shingles) if c206_shingles else ("", 0.0)
        row_max = max(w2_sim, c206_sim)
        max_overall = max(max_overall, row_max)
        rows.append({
            "id": entry["id"],
            "category": entry["category"],
            "w2_nearest": w2_name,
            "w2_similarity": w2_sim,
            "corpus206_nearest": c206_name,
            "corpus206_similarity": c206_sim,
            "max_similarity": row_max,
            "verdict": "contaminated" if row_max >= NEAR_DUP_THRESHOLD else "clean",
        })

    report = {
        "threshold": NEAR_DUP_THRESHOLD,
        "n_theorems": len(manifest),
        "n_w2_survivor_texts": len(w2_texts),
        "n_corpus206_texts": len(corpus206_texts),
        "max_similarity_overall": max_overall,
        "global_verdict": "clean" if max_overall < NEAR_DUP_THRESHOLD else "contaminated",
        "contaminated_ids": [r["id"] for r in rows if r["verdict"] == "contaminated"],
        "rows": rows,
    }
    if out_path is not None:
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(report, indent=2) + "\n")
    return report


# ---------------------------------------------------------------------------
# baseline (0-model floor)
# ---------------------------------------------------------------------------

def _read_done_ids(rows_path: Path) -> set[str]:
    done = set()
    if rows_path.exists():
        with rows_path.open() as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    done.add(json.loads(line)["id"])
                except (json.JSONDecodeError, KeyError):
                    continue
    return done


def run_baseline_tlapm(out_dir: Path, lmgpa_root: Path = DEFAULT_LMGPA_ROOT,
                        manifest: list[dict] | None = None, timeout: int = 600,
                        limit: int | None = None, checker=check_tlapm) -> Path:
    """0-model floor: run tlapm as-is on every manifest module (no repair, no
    model-authored proof). Resumable by id via out_dir/rows.jsonl."""
    manifest = manifest if manifest is not None else load_manifest()
    if limit is not None:
        manifest = manifest[:limit]

    out_dir.mkdir(parents=True, exist_ok=True)
    rows_path = out_dir / "rows.jsonl"
    done = _read_done_ids(rows_path)

    with rows_path.open("a") as out_fh:
        for entry in manifest:
            if entry["id"] in done:
                continue
            mod_path = lmgpa_root / entry["module_file"]
            workdir = out_dir / "work" / entry["id"]
            workdir.mkdir(parents=True, exist_ok=True)
            dest = workdir / mod_path.name
            dest.write_text(mod_path.read_text(errors="replace"))

            status, proved, total, _out, seconds = checker(dest, workdir, timeout=timeout)
            row = {
                "id": entry["id"],
                "status": status,
                "proved": proved,
                "total": total,
                "seconds": seconds,
            }
            out_fh.write(json.dumps(row) + "\n")
            out_fh.flush()
    return rows_path


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(prog="harness.lmgpa_bench")
    sub = ap.add_subparsers(dest="cmd", required=True)

    m = sub.add_parser("manifest", help="rebuild/print the manifest")
    m.add_argument("--lmgpa-root", default=str(DEFAULT_LMGPA_ROOT))
    m.add_argument("--out", default=str(MANIFEST_PATH))

    d = sub.add_parser("decontam", help="Rule-4 near-dup check vs W2 survivors + 206-corpus")
    d.add_argument("--lmgpa-root", default=str(DEFAULT_LMGPA_ROOT))
    d.add_argument("--out", default=str(REPO / "results" / "analysis" / "lmgpa_decontam.json"))

    b = sub.add_parser("baseline", help="0-model tlapm floor over the manifest")
    b.add_argument("--lmgpa-root", default=str(DEFAULT_LMGPA_ROOT))
    b.add_argument("--out-dir", required=True)
    b.add_argument("--timeout", type=int, default=600)
    b.add_argument("--limit", type=int, default=None)

    args = ap.parse_args()

    if args.cmd == "manifest":
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "build_manifest", REPO / "corpus" / "lmgpa" / "build_manifest.py")
        build_manifest = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(build_manifest)
        entries = build_manifest.build(Path(args.lmgpa_root))
        Path(args.out).write_text(json.dumps(entries, indent=2) + "\n")
        print(f"wrote {len(entries)} entries to {args.out}")
    elif args.cmd == "decontam":
        report = decontam_report(lmgpa_root=Path(args.lmgpa_root), out_path=Path(args.out))
        print(f"global_verdict={report['global_verdict']} "
              f"max_similarity={report['max_similarity_overall']:.3f} "
              f"n_theorems={report['n_theorems']} -> {args.out}")
    elif args.cmd == "baseline":
        rows_path = run_baseline_tlapm(Path(args.out_dir), lmgpa_root=Path(args.lmgpa_root),
                                        timeout=args.timeout, limit=args.limit)
        print(f"wrote ledger to {rows_path}")


if __name__ == "__main__":
    main()
