---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "searching", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = Succ[Root]
    /\ pc = "searching"

Explore(v) ==
    /\ v \in frontier
    /\ marked' = marked \cup {v}
    /\ frontier' = (frontier \cup Succ[v]) \ {v}
    /\ pc' = IF frontier = {v} THEN "done" ELSE "searching"

Step ==
    /\ pc = "searching"
    /\ \E v \in frontier : Explore(v)

Done ==
    /\ pc = "done"
    /\ pc' = "idle"
    /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Done

Spec == Init /\ [][Next]_vars

Inv1 == \A v \in marked : Succ[v] \subseteq marked

Inv2 == \A v \in frontier : (v \in marked) => (v = Root \/ \E u \in Nodes : v \in Succ[u] /\ u \in marked)

Inv3 == \A v \in Nodes : v \in marked => (v = Root \/ \E u \in Nodes : v \in Succ[u] /\ u \in marked)

PartialCorrectness == marked = Nodes

Termination == <>(pc = "done")

====