---- MODULE ReachableProofs ----
EXTENDS ReachabilityAlgs, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "working"

Step ==
    /\ pc = "working"
    /\ frontier # {}
    /\ \E s \in frontier:
         /\ marked' = marked \cup {s}
         /\ frontier' = (frontier \ {s}) \cup (Neighbors(s) \ (marked \cup frontier))
    /\ UNCHANGED pc

Finish ==
    /\ pc = "working"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Restart ==
    /\ pc = "done"
    /\ pc' = "working"
    /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Finish \/ Restart

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"working", "done"}
    /\ \A s \in marked: (Neighbors(s) \cap Nodes) \subseteq (marked \cup frontier)

FrontierDisjointFromMarked ==
    \A s \in marked: (Neighbors(s) \cap Nodes) \subseteq (marked \cup frontier)

ReachableDecomposed ==
    Reachable(Root) = marked \cup ReachableFrom(frontier)

SafeStateInvariant ==
    \A s \in Nodes: (Neighbors(s) \cap Nodes) \subseteq (marked \cup frontier)

ReachableFromEmptyIsEmpty ==
    ReachableFrom({}) = {}

ReachableAlgorithmPartialCorrect ==
    (pc = "done") => (Reachable(Root) = marked)

INVARIANTS == {
    TypeOK,
    FrontierDisjointFromMarked,
    ReachableDecomposed,
    SafeStateInvariant,
    ReachableFromEmptyIsEmpty
}

PROPERTIES == {ReachableAlgorithmPartialCorrect}
====