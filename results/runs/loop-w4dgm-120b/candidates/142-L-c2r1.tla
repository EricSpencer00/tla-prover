---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, ReachableDefs, ReachableLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Seen == marked \cup frontier
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"working", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "working"

Mark(n) ==
    /\ pc = "working"
    /\ n \in frontier
    /\ n \notin marked
    /\ marked' = marked \cup {n}
    /\ frontier' = frontier \ {n}
    /\ pc' = pc

Explore(n) ==
    /\ pc = "working"
    /\ n \in marked
    /\ \E m \in Nodes : m \in frontier' /\ m \in Succ(n)
    /\ frontier' \subseteq frontier \cup Succ(n)
    /\ pc' = pc
    /\ UNCHANGED marked

Rest ==
    /\ pc = "working"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : Mark(n) \/ Explore(n)
    \/ Rest \/ Done

Spec == Init /\ [][Next]_vars

Invariant1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ(n) \subseteq Seen
Invariant2 == Reachable(Seen) = Reachable(marked)
Invariant3 == Reachable(Root) = Seen

Theorem Spec => ([]Invariant1 /\ []Invariant2 /\ []Invariant3)
====