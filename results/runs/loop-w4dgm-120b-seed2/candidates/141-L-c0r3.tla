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

Explore(n) ==
    /\ pc = "running"
    /\ n \in frontier
    /\ IF n \notin marked
         THEN /\ marked' = marked \cup {n}
              /\ frontier' = frontier \cup Succ[n]
         ELSE /\ marked' = marked
              /\ frontier' = frontier \ {n}
    /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

Next == \E n \in Nodes : Explore(n)

Spec == Init /\ [][Next]_vars

Inv1 ==
    \A n \in marked : \A m \in Succ[n] : m \in marked \/ m \in frontier

Inv2 ==
    (marked \cup frontier) \cup (frontier # {}) = (marked \cup frontier)

Inv3 ==
    (marked \cup frontier) = (marked \cup frontier)

PartialCorrectness == ReachableFrom({Root}) = marked

Termination == (frontier # {}) ~> (frontier = {})

LimitedSeq == Seq

ConnectedToSomeButNotAll == Succ

====