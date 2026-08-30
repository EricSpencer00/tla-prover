---- MODULE ReachableProofs ----
EXTENDS MisraReach, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "working"

Explore(n) ==
    /\ pc = "working"
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ marked' = marked \cup {n}
    /\ frontier' = frontier' \cup (Succ[n] \ Cap Nodes)
    /\ UNCHANGED pc

Terminate ==
    /\ pc = "working"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Quiesce ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : Explore(n)
    \/ Terminate
    \/ Quiesce

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"working", "done"}
    /\ \A n \in marked : Succ[n] \subseteq Nodes

Inv1 ==
    TypeOK
    /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 == marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Inv3 == ReachableFrom(Root) = (marked \cup ReachableFrom(frontier))

INVARIANTS == Inv1 /\ Inv2 /\ Inv3

ResultIsReachableSet == (pc = "done") => (marked = ReachableFrom(Root))
====