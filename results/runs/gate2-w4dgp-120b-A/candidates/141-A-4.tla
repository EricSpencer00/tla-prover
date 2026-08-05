---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
    IF S = {} THEN {}
    ELSE LET x == CHOOSE y \in S : TRUE
             rest == ReachableFrom(S \ {x})
         IN {x} \cup Succ[x] \cup rest

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

Step ==
    /\ pc = "running"
    /\ frontier # {}
    /\ \E n \in frontier :
         /\ frontier' = (IF n \in marked THEN frontier \ {n} ELSE frontier \cup Succ[n])
         /\ marked' = IF n \in marked THEN marked ELSE marked \cup {n}
    /\ pc' = IF frontier' = {} THEN "done" ELSE pc

Spec == Init /\ [][Step]_vars

Inv1 ==
    \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
    ReachableFrom(marked \cup frontier) = marked \cup ReachableFrom(frontier)

Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness ==
    /\ pc = "done"
    /\ ReachableFrom({Root}) = marked

Termination ==
    WF_vars(Step)

====