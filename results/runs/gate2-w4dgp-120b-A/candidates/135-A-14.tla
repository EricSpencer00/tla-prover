---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "exploring", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = Succ[Root]
    /\ pc = "idle"

Explore ==
    /\ frontier # {}
    /\ marked' = marked \cup frontier
    /\ frontier' = {y \in Nodes : \E x \in frontier : y \in Succ[x]}
    /\ pc' = "exploring"

DoneExplore ==
    /\ frontier = {}
    /\ pc # "done"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ DoneExplore

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

Inv1 ==
    \A x \in frontier : \A y \in Nodes : y \in Succ[x] => y \in marked

Inv2 ==
    \A x \in marked : \E y \in frontier :
        \E i \in Nat :
            Len(i) <= Cardinality(Nodes) /\ y = i[Nat][2] /\ i[Nat][1] = x

Inv3 ==
    marked \cup frontier = Nodes

PartialCorrectness ==
    \A x \in Nodes : x \notin marked => \A y \in frontier : x \notin Succ[y]

Termination == <>(pc = "done")

====