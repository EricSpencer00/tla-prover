---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"searching", "done"}
    /\ Succ \in [Nodes -> SUBSET Nodes]
    /\ Cardinality(Nodes) >= 2
    /\ \A n \in Nodes : Cardinality(Succ[n]) = 2

Init ==
    /\ marked = {Root}
    /\ frontier = Succ[Root]
    /\ pc = "searching"
    /\ Cardinality(Nodes) = 4
    /\ Cardinality(Seq) <= 4

Extend(n) ==
    /\ pc = "searching"
    /\ n \in frontier
    /\ frontier' = (frontier \cup Succ[n]) \ marked
    /\ marked' = marked \cup {n}
    /\ UNCHANGED pc

Complete ==
    /\ pc = "searching"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Extend(_) \/ Complete]_vars

Inv1 ==
    /\ frontier \subseteq Nodes \ marked
    /\ frontier \cap marked = {}

Inv2 == \A n \in marked : \E m \in marked : n # m

Inv3 == marked \cup frontier = Nodes

PartialCorrectness == \A n \in Nodes : n \in marked

Termination == <>(pc = "done")

====