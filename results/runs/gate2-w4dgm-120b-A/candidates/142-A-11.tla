---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachableLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init == marked = {Root} /\ frontier = {} /\ pc = "exploring"

Expand(n) == pc = "exploring" /\ n \in marked /\ \E m \in Nodes \ succ[n] :
                frontier' = frontier \cup {m} /\ UNCHANGED <<marked, pc>>
Mark(m) == pc = "exploring" /\ m \in frontier /\ marked' = marked \cup {frontier}
                /\ frontier' = frontier \ {m} /\ UNCHANGED pc
Idle == pc = "exploring" /\ frontier = {} /\ pc' = "done" /\ UNCHANGED <<marked, frontier>>

Next == \E n \in Nodes : Expand(n) \/ \E m \in Nodes : Mark(m) \/ Idle

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"exploring", "done"}
    /\ \A n \in marked : succ[n] \subseteq marked \cup frontier

Invariant1 == TypeOK /\ \A n \in marked : succ[n] \subseteq marked \cup frontier

Invariant2 == marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Invariant3 == ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

INVARIANTS == {Invariant1, Invariant2, Invariant3}

PartialCorrectness == pc = "done" => marked = ReachableFrom({Root})
====