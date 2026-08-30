---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

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

ExploreStep ==
    /\ pc = "running"
    /\ frontier # {}
    /\ \E n \in frontier :
        \/ (n \notin marked
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ UNCHANGED pc)
        \/ (n \in marked
            /\ frontier' = frontier \ {n}
            /\ UNCHANGED <<marked, pc>>)
    /\ pc' = IF frontier' = {} THEN "done" ELSE pc

Next == ExploreStep

Spec == Init /\ [][Next]_vars

Inv1 ==
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup frontier)
    /\ (marked \cup frontier) \subseteq Nodes

Inv2 ==
    ReachableFrom(Root, marked \cup frontier)
        = ReachableFrom(Root, marked) \cup ReachableFrom(Root, frontier)

Inv3 ==
    ReachableFrom(Root, marked) \cup ReachableFrom(Root, frontier)
        = ReachableFrom(Root, marked \cup frontier)

PartialCorrectness == marked = ReachableFrom(Root, Nodes)

Termination ==
    /\ \A n \in Nodes : Cardinality(Succ[n]) < Cardinality(Nodes)
    /\ WF_vars(ExploreStep)

LimitedSeq(n) == n

====