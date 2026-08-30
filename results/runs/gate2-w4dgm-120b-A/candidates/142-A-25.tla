---- MODULE ReachableProofs ----
EXTENDS MisraReachability, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "working"

Mark(u) ==
    /\ pc = "working"
    /\ u \in frontier
    /\ marked' = marked \cup {u}
    /\ frontier' = frontier \ {u}
    /\ UNCHANGED pc

Expand(u) ==
    /\ pc = "working"
    /\ u \in marked
    /\ u \notin frontier
    /\ \E w \in Nodes : w \notin marked \cup frontier /\ w \in succ[u]
    /\ frontier' = frontier \cup {w}
    /\ UNCHANGED <<marked, pc>>

Terminate ==
    /\ pc = "working"
    /\ frontier = {}
    /\ \A u \in Nodes : u \in marked => succ[u] \subseteq marked
    /\ pc' = "terminated"
    /\ UNCHANGED <<marked, frontier>>

Done ==
    /\ pc = "terminated"
    /\ UNCHANGED vars

Next ==
    \/ \E u \in Nodes : Mark(u)
    \/ \E u \in Nodes : Expand(u)
    \/ Terminate
    \/ Done

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"working", "terminated"}
    /\ \A u \in Nodes : (u \in marked => succ[u] \subseteq marked \cup frontier)

Inv1 == TypeOK /\ (\A u \in marked : succ[u] \subseteq marked \cup frontier)

Inv2 == marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Inv3 == ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

Invariants == Inv1 /\ Inv2 /\ Inv3

PartialCorrectness ==
    (pc = "terminated") => (marked = ReachableFrom({Root}))
====