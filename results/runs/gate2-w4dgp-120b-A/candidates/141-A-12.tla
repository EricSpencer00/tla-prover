---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"start", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "start"

Explore ==
    /\ pc = "start"
    /\ frontier # {}
    /\ \E x \in frontier :
        /\ x \notin marked
        /\ marked' = marked \cup {x}
        /\ frontier' = frontier \cup Succ[x]
    /\ pc' = pc

RemoveFrontier ==
    /\ pc = "start"
    /\ frontier # {}
    /\ \E x \in frontier :
        /\ x \in marked
        /\ frontier' = frontier \ {x}
    /\ pc' = pc

Terminate ==
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ RemoveFrontier \/ Terminate

Spec == Init /\ [][Next]_vars

Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 == ReachableFromSet(marked) \cup ReachableFromSet(frontier) = ReachableFromSet(marked \cup frontier)

Inv3 == ReachableFromSet({Root}) = marked \cup ReachableFromSet(frontier)

PartialCorrectness == pc = "done" => ReachableFromSet({Root}) = marked

FiniteReach == ReachableFromSet({Root}) \in FINITE

Termination == FiniteReach ~> (pc = "done")

====