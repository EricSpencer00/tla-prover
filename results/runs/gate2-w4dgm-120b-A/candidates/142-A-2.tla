---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachableAlgs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeCorrect ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "active"}

ReachableFrom(S) == {n \in Nodes : \E m \in S : Root ~> m ~> n}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "idle"

Explore(n) ==
    /\ pc = "idle"
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ marked' = marked \cup {n}
    /\ pc' = "active"

Deposit(m) ==
    /\ pc = "active"
    /\ m \notin marked
    /\ m \notin frontier
    /\ frontier' = frontier \cup {m}
    /\ pc' = "idle"

Discard(n) ==
    /\ pc = "active"
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ pc' = "idle"

Reaches ==
    /\ pc = "idle"
    /\ frontier = {}
    /\ frontier' = {Root}
    /\ marked' = {}
    /\ pc' = pc

Next ==
    \/ \E n \in Nodes : Explore(n)
    \/ \E m \in Nodes : Deposit(m)
    \/ \E n \in Nodes : Discard(n)
    \/ Reaches

Spec == Init /\ [][Next]_vars

Invariant1 ==
    TypeCorrect /\ \A n \in marked : {m \in Nodes : n ~> m} \subseteq (marked \cup frontier)

Invariant2 == (marked \cup ReachableFrom(frontier)) = ReachableFrom(marked \cup frontier)

Invariant3 == ReachableFrom({Root}) = (marked \cup ReachableFrom(frontier))

PartialCorrectness == (frontier = {}) ~> (marked = ReachableFrom({Root}))

INVARIANTS == {Invariant1, Invariant2, Invariant3}
PROPERTIES == {PartialCorrectness}
====