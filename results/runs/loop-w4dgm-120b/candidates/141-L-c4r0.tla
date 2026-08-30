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
    /\ PCCase
    /\ pc' = pc
    /\ UNCHANGED <<marked, frontier>>

PCCase ==
    \/ \E n \in frontier :
        /\ n \notin marked
        /\ marked' = marked \cup {n}
        /\ frontier' = frontier \cup Succ[n]
    \/ \E n \in frontier :
        /\ n \in marked
        /\ frontier' = frontier \ {n}
        /\ marked' = marked

ExploreN == Explore /\ UNCHANGED pc

Next == ExploreN

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(ExploreN)

Inv1 ==
    \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
    (marked \cup frontier) \subseteq {Root} \cup (Union_{n \in marked \cup frontier} Succ[n])

Inv3 ==
    {Root} \cup (Union_{n \in frontier} Succ[n]) \subseteq marked \cup (Union_{n \in frontier} Succ[n])

PartialCorrectness ==
    \A n \in reachable(Root) : n \in marked

Termination ==
    (reachable(Root) # Nodes) ~> (frontier = {})

PC == IF frontier = {} THEN "done" ELSE "running"

====