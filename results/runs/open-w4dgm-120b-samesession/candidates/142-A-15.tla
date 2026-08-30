---- MODULE ReachableProofs ----
EXTENDS MisraReach, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeInv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"working", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "working"

Mark(v) ==
    /\ pc = "working"
    /\ v \notin marked
    /\ v \notin frontier
    /\ frontier' = frontier \cup {v}
    /\ UNCHANGED <<marked, pc>>

Commit(v) ==
    /\ pc = "working"
    /\ v \in frontier
    /\ frontier' = frontier \ {v}
    /\ marked' = marked \cup {v}
    /\ UNCHANGED pc

Terminate ==
    /\ pc = "working"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E v \in Nodes : Mark(v)
    \/ \E v \in Nodes : Commit(v)
    \/ Terminate

Spec == Init /\ [][Next]_vars

Invariant1 ==
    /\ TypeInv
    /\ \A u \in marked : \A v \in Nodes : (u -> v) => (v \in marked \/ v \in frontier)

Invariant2 ==
    /(marked \cup (ReachableFrom(frontier))) = ReachableFrom(marked \cup frontier)

Invariant3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

AllProofs == Invariant1 /\ Invariant2 /\ Invariant3

PartialCorrectness ==
    (pc = "done") => (marked = ReachableFrom({Root}))
====