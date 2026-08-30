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

Next ==
    \E n \in Nodes : Explore(n)

Spec == Init /\ [][Next]_vars

Inv1 ==
    \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
    (marked \cup frontier) = Nodes

Inv3 ==
    Nodes = marked \cup {m \in Nodes : \E n \in frontier : m \in Succ[n]}

PartialCorrectness == Inv3

Termination == (frontier # {}) ~> (frontier = {})

\* The .cfg substitutes ConnectedToSomeButNotAll for Succ, and LimitedSeq for Seq.
ConnectedToSomeButNotAll(n) == Succ[n]
LimitedSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : TRUE

====