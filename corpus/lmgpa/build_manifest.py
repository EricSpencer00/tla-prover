"""One-off script that produced corpus/lmgpa/manifest.json from the lmgpa
checkout. Kept for reproducibility; not part of the harness CLI.

Usage: python3 corpus/lmgpa/build_manifest.py [--lmgpa-root /Users/eric/GitHub/lmgpa]
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent
DEFAULT_LMGPA_ROOT = Path("/Users/eric/GitHub/lmgpa")


def find_theorem_name(text: str, stem: str) -> str:
    """The 'main' benchmark theorem: named after the file stem (math
    categories) or literally 'Inductiveness' (distributed_ind_inv)."""
    if re.search(rf"^THEOREM\s+{re.escape(stem)}\b", text, re.MULTILINE):
        return stem
    if re.search(r"^THEOREM\s+Inductiveness\b", text, re.MULTILINE):
        return "Inductiveness"
    # fallback: last THEOREM declared in the file
    names = re.findall(r"^THEOREM\s+([A-Za-z0-9_]+)\s*==", text, re.MULTILINE)
    return names[-1] if names else ""


def build(lmgpa_root: Path) -> list[dict]:
    entries = []
    for f in sorted((lmgpa_root / "benchmarks").rglob("*.tla")):
        rel = f.relative_to(lmgpa_root)
        category = rel.parts[1] if len(rel.parts) > 2 else rel.parts[0]
        # category = top-level benchmark family; math has minif2f/proofnet subdirs
        if rel.parts[0] == "benchmarks":
            parts = rel.parts[1:]
        else:
            parts = rel.parts
        category = "/".join(parts[:-1]) if len(parts) > 1 else parts[0]
        text = f.read_text(errors="replace")
        theorem_name = find_theorem_name(text, f.stem)
        entries.append({
            "id": f.stem,
            "category": category,
            "module_file": str(rel),
            "theorem_name": theorem_name,
            "sha256": hashlib.sha256(f.read_bytes()).hexdigest(),
        })
    return entries


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lmgpa-root", default=str(DEFAULT_LMGPA_ROOT))
    ap.add_argument("--out", default=str(REPO / "corpus" / "lmgpa" / "manifest.json"))
    args = ap.parse_args()
    entries = build(Path(args.lmgpa_root))
    out = Path(args.out)
    out.write_text(json.dumps(entries, indent=2) + "\n")
    print(f"wrote {len(entries)} entries to {out}")


if __name__ == "__main__":
    main()
