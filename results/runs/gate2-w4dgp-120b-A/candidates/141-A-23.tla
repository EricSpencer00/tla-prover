---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

BEGINNING == "beginning"
DONE == "done"

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {BEGINNING, DONE}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = BEGINNING

ExploreFrontier ==
    /\ frontier # {}
    /\ \E n \in frontier :
        IF n \notin marked
        THEN /\ marked' = marked \cup {n}
             /\ frontier' = frontier \cup Succ[n]
        ELSE /\ marked' = marked
             /\ frontier' = frontier \ {n}
    /\ pc' = BEGINNING

Terminate ==
    /\ frontier = {}
    /\ pc = BEGINNING
    /\ pc' = DONE
    /\ UNCHANGED <<marked, frontier>>

Exploring == ExploreFrontier \/ Terminate

Spec == /\ Init
        /\ [][Exploring]_vars
        /\ WF_vars(ExploreFrontier)

Inv1 ==
    \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
    (marked \cup frontier) \cup
        (CHOOSE S \in {S \in SUBSET Nodes : {Root} \subseteq S} :
            \A m \in S : Succ[m] \subseteq S) =
    CHOOSE S \in {S \in SUBSET Nodes : {Root} \subseteq S} :
        \A m \in S : Succ[m] \subseteq S

Inv3 ==
    \A S \in {S \in SUBSET Nodes : {Root} \subseteq S} :
        S = marked \cup {n \in S : \E m \in frontier : n \in Succ[m]}

PartialCorrectness == (pc = DONE) => (marked = ConnectedToSomeButNotAll)
ReachableNodesFinite == ConnectedToSomeButNotAll # Nodes
Termination == ReachableNodesFinite ~> (pc = DONE)
====