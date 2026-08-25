---- MODULE ReachableProofs ----
EXTENDS SeqReach, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

vars == <<Marked, Frontier, pc>>

INIT ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "init"

NEXT ==
  TRUE

(* Invariant 1: type correctness and successor condition *)
Inv1 ==
  /\ Marked ⊆ Nodes
  /\ Frontier ⊆ Nodes
  /\ ∀ n ∈ Marked :
        ∀ s ∈ Succ[n] :
            s ∈ Marked ∨ s ∈ Frontier

(* Invariant 2: marked ∪ reachable‑from‑frontier = reachable‑from‑marked∪frontier *)
Inv2 ==
  ReachableFrom(Marked) ∪ ReachableFrom(Frontier) = ReachableFrom(Marked ∪ Frontier)

(* Invariant 3: reachable from root = marked ∪ reachable‑from‑frontier *)
Inv3 ==
  ReachableFrom({Root}) = Marked ∪ ReachableFrom(Frontier)

INVARIANTS == /\ Inv1 /\ Inv2 /\ Inv3

(* Partial‑correctness property: on termination the marked set equals the reachable set *)
PROPERTIES ==
  (pc = "done") ⇒ (Marked = ReachableFrom({Root}))

SPEC ==
  INIT /\ [][NEXT]_vars

====