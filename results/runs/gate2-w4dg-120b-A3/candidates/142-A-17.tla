---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Reachability

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "spread"

SpreadStep ==
    /\ pc = "spread"
    /\ frontier # {}
    /\ \E n \in frontier :
         /\ marked' = marked \cup {n}
         /\ frontier' = (frontier \ {n}) \cup (Successors(n) \ (marked \cup frontier))
    /\ pc' = "spread"

HaltStep ==
    /\ frontier = {}
    /\ pc = "spread"
    /\ pc' = "halted"
    /\ UNCHANGED <<marked, frontier>>

INIT == Init
NEXT == SpreadStep \/ HaltStep

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"spread", "halted"}

FrontierClosed ==
    /\ marked \subseteq (marked \cup frontier)
    /\ \A n \in marked : Successors(n) \subseteq (marked \cup frontier)

ReachableDecomposition ==
    marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

ReachableCovering ==
    ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

Spec == INIT /\ [][NEXT]_vars

Invariants ==
    /\ TypeOK
    /\ FrontierClosed
    /\ ReachableDecomposition
    /\ ReachableCovering

Properties ==
    /\ FrontierClosed
    /\ ReachableDecomposition
    /\ ReachableCovering

====