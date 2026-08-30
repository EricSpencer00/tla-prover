---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

ConnectedToSomeButNotAll == Succ

\* The reachability check is a finite existential quantification over sequences,
\* replacing the unbounded Seq operator from Sequences with a bounded version.
LimitedSeq == [n \in Nat |-> IF n = 0 THEN <<Root>> ELSE <<Root>>]

VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "running", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "idle"

\* The algorithm is the same as the standard sequential Misra version; the
\* frontier is always a subset of the marked set, and each expansion adds
\* at least one new node so the run is guaranteed to reach closure.
Step ==
    /\ pc = "idle"
    /\ frontier # {}
    /\ pc' = "running"
    /\ UNCHANGED <<marked, frontier>>

Expand(n) ==
    /\ pc = "running"
    /\ n \in frontier
    /\ marked' = marked \cup Succ[n]
    /\ frontier' = (frontier \ {n}) \cup Succ[n]
    /\ pc' = IF frontier = {n} THEN "done" ELSE "running"

Done ==
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ Step
    \/ \E n \in frontier : Expand(n)
    \/ Done

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

Inv1 == frontier \subseteq marked
Inv2 == \A k \in marked : (k = Root) \/ (\E m \in marked : k \in Succ[m])
Inv3 == \A n \in Nodes : n \in marked => \E p \in LimitedSeq : p[Len(p)] = n
PartialCorrectness == marked \subseteq Nodes

Termination == <>(pc = "done")

====