---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

Explore ==
    /\ frontier # {}
    /\ \E n \in frontier :
        \/ /\ n \notin marked
           /\ marked' = marked \cup {n}
           /\ frontier' = frontier \cup Succ[n]
        \/ /\ n \in marked
           /\ frontier' = frontier \ {n}
           /\ marked' = marked
    /\ pc' = pc
    /\ UNCHANGED pc

ExploreN == Explore /\ UNCHANGED pc

Next == ExploreN

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(ExploreN)

Inv1 ==
    \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
    (marked \cup frontier) \subseteq {Root} \cup Union({Succ[n] : n \in marked \cup frontier})

Inv3 ==
    {Root} \cup Union({Succ[n] : n \in frontier}) \subseteq marked \cup Union({Succ[n] : n \in frontier})

reachable(x) == {x} \cup Union({Succ[n] : n \in reachable(x)})

PartialCorrectness ==
    \A n \in reachable(Root) : n \in marked

Termination ==
    (reachable(Root) # Nodes) ~> (frontier = {})

PC == IF frontier = {} THEN "done" ELSE "running"

====