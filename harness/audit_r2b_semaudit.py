"""Rule-9 semantic audit for any candidate-persisted framing-B run.

Default arms are the E2.c framing-B r2 baseline; pass run dirs on the command
line to audit a challenger arm at the same bar (Amendment 26).

For every passing row in the run's rows.jsonl:
  1. verify candidate_sha256 matches the candidate file on disk (integrity)
  2. diff the candidate module against the CANONICAL (uncorrupted) spec text
     (gen_eval.canonical_spec_text), using semaudit.py's checked_names/
     dep_closure/normalize machinery against the reference .cfg
  3. confirm the mutated site (mutation_record: original/replacement/offset)
     is actually restored/fixed in the candidate, not deleted/bypassed
  4. flag CLEAN/REVIEW/STRUCTURAL like semaudit.py; anything REVIEW/STRUCTURAL
     needs a manual read
"""
import hashlib
import json
import sys
from pathlib import Path

REPO = Path("/Users/eric/GitHub/prove-TLA")
CORPUS = Path("/Users/eric/GitHub/tla_benchmark/data")
sys.path.insert(0, str(REPO))

from harness.semaudit import checked_names, dep_closure, normalize
from harness.repair import extract_definitions, extract_candidate, resolve_cfg
from harness.gen_eval import canonical_spec_text

CFG_DIRS = [("override", REPO / "corpus" / "configs" / "overrides"),
            ("original", CORPUS / "cfg"),
            ("draft", REPO / "corpus" / "configs" / "drafts")]


def audit_arm(arm=None, rundir=None):
    if rundir is None:
        rundir = REPO / "results" / "runs" / f"e2c-baseline-r2-{arm}-b"
    rundir = Path(rundir)
    rows = [json.loads(l) for l in (rundir / "rows.jsonl").read_text().splitlines() if l]
    passing = [r for r in rows if r["verdict"] == "pass"]

    sha_mismatches = []
    results = []
    for r in passing:
        spec = r["spec"]
        cand_path = rundir / r["candidate_path"]
        cand_text = cand_path.read_text(errors="replace")
        actual_sha = hashlib.sha256(cand_text.encode()).hexdigest()
        if actual_sha != r["candidate_sha256"]:
            sha_mismatches.append((spec, r["sample"], r["candidate_sha256"], actual_sha))

        canon = canonical_spec_text(spec, CORPUS)
        canon_mod = extract_candidate(canon) or canon
        cand_mod = extract_candidate(cand_text) or cand_text

        cfg_text, _ = resolve_cfg(spec, CFG_DIRS)
        inv_names, struct_names = checked_names(cfg_text or "")

        ob = extract_definitions(canon_mod)
        cb = extract_definitions(cand_mod)
        changed = {n for n in set(ob) | set(cb)
                   if normalize(ob.get(n, "")) != normalize(cb.get(n, ""))}
        inv_closure = dep_closure(inv_names, ob) | dep_closure(inv_names, cb)
        struct_closure = dep_closure(struct_names, ob) | dep_closure(struct_names, cb)
        touched_checked = sorted(changed & inv_closure)
        touched_struct = sorted(changed & struct_closure)

        # was the mutated site itself among the changed defs? locate which def
        # contains the mutation offset in canon_mod
        mut = r.get("mutation_record", {})
        mut_off = mut.get("offset")
        mut_def = None
        if mut_off is not None:
            for name, block in ob.items():
                idx = canon_mod.find(block)
                if idx != -1 and idx <= mut_off <= idx + len(block):
                    mut_def = name
                    break

        if touched_struct:
            verdict = "STRUCTURAL"
        elif touched_checked:
            verdict = "REVIEW"
        else:
            verdict = "CLEAN"

        # does the candidate still contain the corrupted replacement text
        # verbatim at a definition that matches mut_def (bypass/no-op check)?
        replacement_present = False
        if mut.get("replacement") and mut_def and mut_def in cb:
            replacement_present = mut["replacement"] in cb[mut_def] and \
                normalize(cb.get(mut_def, "")) == normalize(ob.get(mut_def, "").replace(
                    mut.get("original", ""), mut.get("replacement", "")))

        results.append({
            "spec": spec, "sample": r["sample"], "verdict": verdict,
            "checked_names": sorted(inv_names), "structural_names": sorted(struct_names),
            "touched_checked": touched_checked, "touched_structural": touched_struct,
            "total_changed": sorted(changed),
            "mutation": mut.get("mutation"), "mut_def": mut_def,
            "replacement_still_present": replacement_present,
            "candidate_path": r["candidate_path"],
        })
    return passing, results, sha_mismatches


if __name__ == "__main__":
    args = sys.argv[1:]
    if args:
        arms = [(Path(a).name, Path(a)) for a in args]
        out_path = REPO / "results" / "runs" / "challenger_b_audit_raw.json"
    else:
        arms = [(a, None) for a in ("20b", "120b")]
        out_path = REPO / "results" / "runs" / "r2b_audit_raw.json"
    all_out = {}
    for label, rundir in arms:
        passing, results, sha_mismatches = audit_arm(label, rundir)
        all_out[label] = {"n_passing": len(passing), "results": results,
                          "sha_mismatches": sha_mismatches}
        n_clean = sum(1 for x in results if x["verdict"] == "CLEAN")
        n_review = sum(1 for x in results if x["verdict"] != "CLEAN")
        print(f"== {label} == passing={len(passing)} CLEAN={n_clean} "
              f"REVIEW/STRUCTURAL={n_review} sha_mismatches={len(sha_mismatches)}")
    out_path.write_text(json.dumps(all_out, indent=2))
    print("wrote", out_path)
