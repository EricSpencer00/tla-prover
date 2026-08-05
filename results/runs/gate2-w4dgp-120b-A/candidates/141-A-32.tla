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

ReachableFrom(S) == {y \in Nodes: \E x \in S : y \in Succ[x]}

Nxt(S) == ReachableFrom(S) \cup S

PartialCorrectness ==
    \A S \subseteq Nodes :
        (S \cup frontier = S \cup ReachableFrom(frontier))
            => (ReachableFrom(S) = S)

Inv1 ==
    \A x \in marked : ReachableFrom({x}) \subseteq marked \cup frontier

Inv2 ==
    (marked \cup frontier) \cup ReachableFrom(frontier) =
        ReachableFrom(marked \cup frontier)

Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

Explore ==
    /\ pc = "running"
    /\ frontier # {}
    /\ \E x \in frontier :
        \/ /\ x \notin marked
           /\ marked' = marked \cup {x}
           /\ frontier' = frontier \cup Succ[x]
        \/ /\ x \in marked
           /\ frontier' = frontier \ {x}
    /\ UNCHANGED pc

Done ==
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

Termination == (ReachableFrom({Root}) # {}) ~> (frontier = {})

LimitedSeq == Seq
====