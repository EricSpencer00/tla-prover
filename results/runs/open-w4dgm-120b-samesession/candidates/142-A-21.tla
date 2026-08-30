---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "growing", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "idle"

Explore(n) ==
    /\ pc = "idle"
    /\ n \in marked
    /\ frontier' = frontier \cup {n}
    /\ pc' = "growing"
    /\ UNCHANGED marked

Grow(n) ==
    /\ pc = "growing"
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ marked' = marked \cup {n}
    /\ pc' = "idle"
    /\ UNCHANGED <<>>

Complete ==
    /\ frontier = {}
    /\ \A n \in Nodes : n \in marked => \A e \in Edges[n] : e \in marked \/ frontier
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

InitState == Init
NextState ==
    \/ \E n \in Nodes : Explore(n)
    \/ \E n \in Nodes : Grow(n)
    \/ Complete

Spec == Init /\ [][NextState]_<<marked, frontier, pc>>

Invariant1 == TypeOK /\ \A n \in marked : \A e \in Edges[n] : e \in marked \/ frontier
Invariant2 == (marked \cup frontier) \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)
Invariant3 == ReachFrom(Root) = marked \cup ReachFrom(frontier)
FinalState == pc = "done" => ReachFrom(Root) = marked

INVARIANTS == {Invariant1, Invariant2, Invariant3}
PROPERTIES == {FinalState}
====