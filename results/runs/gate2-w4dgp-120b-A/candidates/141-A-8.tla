---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
    IF S = {} THEN {}
    ELSE LET x == CHOOSE y \in S : TRUE IN Succ[x] \cup ReachFrom(S \ {x})

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

Explore ==
    /\ pc = "running"
    /\ frontier # {}
    /\ \E n \in frontier :
        \/ /\ n \notin marked
           /\ marked' = marked \cup {n}
           /\ frontier' = frontier \cup Succ[n]
        \/ /\ n \in marked
           /\ frontier' = frontier \ {n}
           /\ marked' = marked
    /\ pc' = "running"

Finish ==
    /\ frontier = {}
    /\ pc = "running"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Finish

Inv1 ==
    \A m \in marked : Succ[m] \subseteq (marked \cup frontier)

Inv2 ==
    ReachFrom(marked \cup frontier) = ReachFrom(marked) \cup ReachFrom(frontier)

Inv3 ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

PartialCorrectness == pc = "done" => marked = ReachFrom({Root})

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

Termination == finite(ReachFrom({Root})) ~> (pc = "done")

====