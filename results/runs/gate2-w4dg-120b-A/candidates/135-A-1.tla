---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {"done", "running"}

Init ==
    /\ marked = {Root}
    /\ frontier = Succ[Root]
    /\ pc = "running"

Step ==
    /\ pc = "running"
    /\ frontier # {}
    /\ \E n \in frontier :
         /\ marked' = marked \cup {n}
         /\ frontier' = (frontier \cup Succ[n]) \ marked
    /\ UNCHANGED pc

Terminate ==
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Terminate

Spec == Init /\ [][Next]_vars

Inv1 == frontier \subseteq Nodes \ marked
Inv2 == marked \subseteq {n \in Nodes : \E m \in marked : n \in Succ[m]}
Inv3 == {n \in Nodes : \E s \in Seq : \A i \in DOMAIN s : s[i] \in MarkedAt(i)} = marked
MarkedAt(k) == IF k = 0 THEN {Root} ELSE frontier \cup marked
PartialCorrectness == (pc = "done") => (marked = Nodes)

Termination == <>(pc = "done")
====