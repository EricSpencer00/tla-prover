---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

Visit(n) ==
    /\ n \in frontier
    /\ n \notin marked
    /\ marked' = marked \cup {n}
    /\ frontier' = frontier \cup Succ[n]
    /\ pc' = pc

Drop(n) ==
    /\ n \in frontier
    /\ n \in marked
    /\ frontier' = frontier \ {n}
    /\ marked' = marked
    /\ pc' = pc

Next ==
    \/ \E n \in Nodes : Visit(n)
    \/ \E n \in Nodes : Drop(n)
    \/ /\ frontier = {}
       /\ pc = "running"
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Inv1 ==
    \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
    (marked \cup frontier) \cup Seq = (marked \cup frontier)

Inv3 ==
    marked \cup (frontier \cup Seq) = (marked \cup frontier)

PartialCorrectness ==
    (pc = "done") => (marked = (marked \cup frontier) \cup Seq)

Termination ==
    (marked \cup frontier) \cup Seq = (marked \cup frontier)

====