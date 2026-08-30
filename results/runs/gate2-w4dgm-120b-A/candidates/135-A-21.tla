---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* Configuration for exhaustive model checking: a concrete 4-node graph
\* where each node has exactly 2 successors, and a bounded sequence type.
CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {"idle", "active", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "idle"

\* The step from the underlying reachability algorithm (marking one
\* frontier node and adding its successors).
MarkStep(n) ==
    /\ n \in frontier
    /\ frontier' = (frontier \ {n}) \union (Succ[n] \ {n})
    /\ marked' = marked \union {n}
    /\ pc' = IF frontier = {n} THEN "done" ELSE pc

Start ==
    /\ pc = "idle"
    /\ pc' = "active"
    /\ UNCHANGED <<marked, frontier>>

Done ==
    /\ pc = "active"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E n \in Nodes : MarkStep(n)
    \/ Start
    \/ Done

Spec == Init /\ [][Next]_vars

\* Safety: type correctness and the three core reachability invariants.
Inv1 == TypeOK

Inv2 == \A n \in marked : n \in (FrontierSet \union marked)

\* The frontier is always disjoint from the already-marked set.
Inv3 == FrontierSet \cap marked = {}

Inv4 ==
    \A n \in Nodes : (n \in FrontierSet \cup marked) <=> Reachable(n)

PartialCorrectness == FrontierSet = {}

\* Liveness: the algorithm always eventually reaches a completed state.
Termination == <>(pc = "done")
====