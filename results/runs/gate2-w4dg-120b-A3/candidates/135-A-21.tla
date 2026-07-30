---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* The override below makes every sequence of at most |Nodes| elements a
\* primitive, so the "exists a sequence x in Seq(Nodes)" quantifier stays finite.
\* Seq is still in scope via EXTENDS Sequences, but ONLY this FINITE version is used.
LimitedSeq == UNION { [1 .. n -> Nodes] : n \in 0 .. Cardinality(Nodes) }

StateSpace == [marked: SUBSET Nodes, frontier: SUBSET Nodes, pc: {"idle", "working", "done"}]

Init == [marked |-> {Root}, frontier |-> {Root}, pc |-> "working"]

Explore ==
    /\ pc = "working"
    /\ \E w \in frontier :
        /\ marked' = marked \cup Succ[w]
        /\ frontier' = (frontier \cup Succ[w]) \ {w}
    /\ pc' = IF frontier = {} THEN "done" ELSE "working"

Spec == Init /\ [][Explore]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "working", "done"}

Inv1 ==
    \A x \in Nodes : x \in marked => \E y \in Nodes : x \in Succ[y]

Inv2 ==
    \A x \in Nodes : x \in frontier => x \in marked

Inv3 ==
    \A x \in Nodes : x \in marked => (x \in frontier \/ \E y \in Nodes : x \in Succ[y])

PartialCorrectness ==
    \A x \in Nodes : x \in marked => \E y \in Nodes : x \in Succ[y]

Termination ==
    <>(pc = "done")

====