"""W4.1 -- scenario-lattice seed generation + verified spec funnel.

Eric 2026-07-17: "generate a ton of specs from general reasoning intelligence
... throw it at the flywheel". Design doc: docs/designs/2026-07-17-cross-
family-flywheel.md. CAVEAT ledgered there and here: scenarios AND specs from
the same family as any future student reintroduces the self-loop at the seed
level; the mitigation in THIS module is that novelty is forced by a
combinatorial lattice sampled deterministically -- the model instantiates
cells it did not choose. Any TRAIN run on this corpus remains gated by
Amendment 17 (one pre-registered 120b eval, corpus-size floor).

Pipeline per lattice cell:
  1. scenario prompt (domain x mechanism x property x twist) -> NL description
     with a SAFETY PROPERTY: section (harness.w2_loop.parse_nl contract).
  2. NL -> spec via the EXISTING W2 loop (harness.w2_loop.run_loop_for_seed):
     SANY + non-vacuous TLC + mutation battery + fidelity gates, repair
     iterations included. Nothing about the gates is new or weakened.
  3. decontam vs canonical corpora (load_canonical), same threshold.
Survivor rows land in w2_survivors.jsonl format (corpus_prep-compatible).

Resumable: cell key in the attempts ledger is skipped on restart.
"""
import argparse
import hashlib
import itertools
import json
import random
import time
from pathlib import Path

from .w2_loop import NLMissingProperty, parse_nl, run_loop_for_seed

DOMAINS = [
    "a hospital operating-room scheduler", "an air-traffic runway allocator",
    "a warehouse robot fleet", "a bank's interbank settlement batch",
    "a car-wash conveyor line", "a multiplayer game lobby matchmaker",
    "an elevator bank in a skyscraper", "a container-ship crane yard",
    "a university course-registration system", "a power-grid load shedder",
    "a subway signalling block system", "a print shop job spooler",
    "a blood-bank inventory tracker", "a vending machine network",
    "a wildfire drone surveillance swarm", "a stock exchange opening auction",
    "a pharmacy prescription dispenser", "an airport baggage router",
    "a smart-home door lock network", "a library book reservation system",
]
MECHANISMS = [
    "optimistic locking with retry", "a token ring granting exclusive access",
    "two-phase commit across participants", "leader election with failover",
    "a bounded work queue with backpressure", "quorum voting on each action",
    "lease-based ownership with expiry", "a compare-and-swap register",
    "hierarchical locks (coarse then fine)", "epoch-numbered reconfiguration",
]
PROPERTIES = [
    "mutual exclusion of a critical resource",
    "no lost updates to a shared record",
    "conservation of a quantity (nothing created or destroyed)",
    "no double allocation of the same slot",
    "bounded capacity is never exceeded",
    "an irreversible action happens at most once",
    "no action by an unauthorized or stale participant",
]
TWISTS = [
    "one participant can crash silently", "messages can be reordered",
    "two independent instances share one pool", "a participant can be slow but not failed",
    "capacity changes at runtime", "there is a privileged admin override",
]

SCENARIO_PROMPT = """You are generating a REQUIREMENTS description for a formal
specification exercise. Setting: {domain}. Coordination mechanism: {mechanism}.
Complication: {twist}.

Write 5-9 sentences of plain English (NO TLA+, no math notation) describing a
small concurrent/distributed protocol in this setting: the participants, the
state they maintain, the steps they may take, and how the mechanism coordinates
them under the complication. Keep it small enough to model with 2-4 state
variables. Make the protocol concrete and specific to the setting -- name the
resources and roles.

End with exactly one section formatted as:
SAFETY PROPERTY: <one sentence stating, in this scenario's terms, {prop}>"""


def lattice(seed: int, n: int):
    """Deterministic sample of n distinct lattice cells."""
    cells = list(itertools.product(range(len(DOMAINS)), range(len(MECHANISMS)),
                                   range(len(PROPERTIES)), range(len(TWISTS))))
    rng = random.Random(seed)
    rng.shuffle(cells)
    return cells[:n]


def cell_key(c) -> str:
    return f"d{c[0]}-m{c[1]}-p{c[2]}-t{c[3]}"


def module_name_for(c) -> str:
    return f"W4C{c[0]}x{c[1]}x{c[2]}x{c[3]}"


def run_w4(model, out_dir: Path, n_cells: int, lattice_seed: int = 20260717,
           timeout: int = 60, max_iters: int = 4, canon=None):
    from .w21_funnel import load_canonical
    out_dir = Path(out_dir).resolve()   # ABSOLUTE (java.io.tmpdir trap, 2026-07-16)
    out_dir.mkdir(parents=True, exist_ok=True)
    attempts = out_dir / "w4_attempts.jsonl"
    survivors = out_dir / "w2_survivors.jsonl"   # corpus_prep-compatible name
    done = set()
    if attempts.exists():
        # nl_missing_property rejects cost one generation -- retry them on
        # resume instead of burying the cell forever
        done = {r["cell"] for r in map(json.loads,
                (l for l in attempts.read_text().splitlines() if l.strip()))
                if r.get("rejection_reason") != "nl_missing_property"}
    if canon is None:
        canon = load_canonical()
    from .w2_loop import decontam_survivor

    cells = [c for c in lattice(lattice_seed, n_cells) if cell_key(c) not in done]
    n_surv = 0
    import os
    import threading
    from concurrent.futures import ThreadPoolExecutor, as_completed
    lock = threading.Lock()
    conc = int(os.environ.get("GEN_EVAL_CONCURRENCY", "1"))

    def one(c):
        key = cell_key(c)
        prompt = SCENARIO_PROMPT.format(
            domain=DOMAINS[c[0]], mechanism=MECHANISMS[c[1]],
            prop=PROPERTIES[c[2]], twist=TWISTS[c[3]])
        base = {"cell": key, "timestamp": time.time(), "model": model.id}
        nl = None
        for _try in range(3):
            [reply] = model.generate(prompt, 1, 1.0, 2048)
            try:
                nl = parse_nl(reply)
                break
            except NLMissingProperty:
                continue
        if nl is None:
            return {**base, "survived": False,
                    "rejection_reason": "nl_missing_property"}
        wd = out_dir / "work" / key
        wd.mkdir(parents=True, exist_ok=True)
        r = run_loop_for_seed(model, nl, module_name_for(c), wd,
                              timeout=timeout, max_iters=max_iters)
        if r["survived"]:
            verdict, score = decontam_survivor(r["spec_text"], canon)
            if verdict != "clean":
                r = {**r, "survived": False,
                     "rejection_reason": f"decontam:{score:.2f}"}
        return {**base, "seed_key": f"w4::{key}", "nl": nl, **r}

    with open(attempts, "a") as af, open(survivors, "a") as sf, \
            ThreadPoolExecutor(max_workers=max(1, conc)) as pool:
        futs = {pool.submit(one, c): c for c in cells}
        for i, fut in enumerate(as_completed(futs), 1):
            row = fut.result()
            with lock:
                af.write(json.dumps(row) + "\n")
                af.flush()
                if row["survived"]:
                    sf.write(json.dumps(row) + "\n")
                    sf.flush()
                    n_surv += 1
            print(f"[{i}/{len(cells)}] {row['cell']}: survived={row['survived']} "
                  f"(total {n_surv})", flush=True)
    print(f"W4 funnel: {n_surv} survivors this run -> {survivors}")
    return n_surv


def main(argv=None):
    ap = argparse.ArgumentParser(prog="python3 -m harness.w4_scenarios")
    ap.add_argument("--out", required=True)
    ap.add_argument("--model", required=True)
    ap.add_argument("--n-cells", type=int, default=400)
    ap.add_argument("--lattice-seed", type=int, default=20260717)
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--max-iters", type=int, default=4)
    a = ap.parse_args(argv)
    from .repair import make_model
    run_w4(make_model(a.model), Path(a.out), a.n_cells, a.lattice_seed,
           a.timeout, a.max_iters)


if __name__ == "__main__":
    main()
