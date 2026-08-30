---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "start"

Explore(r) ==
    /\ pc = "start"
    /\ r \in frontier
    /\ r \notin marked
    /\ marked' = marked \cup {r}
    /\ frontier' = frontier \cup Succ[r]
    /\ pc' = "start"

Stall ==
    /\ pc = "start"
    /\ frontier \subseteq marked
    /\ frontier # {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E r \in Nodes : Explore(r)
    \/ Stall

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"start", "done"}

Inv1 ==
    frontier \subseteq Succ[marked]

Inv2 ==
    marked \subseteq UNION {Succ[s] : s \in marked}

Inv3 ==
    marked = UNION {Succ[s] : s \in marked}

PartialCorrectness ==
    (\A r \in Nodes : r \in marked => r \in Succ[marked])
        => frontier \subseteq marked

Termination ==
    \A r \in Nodes : (r \in frontier) ~> (r \in marked)

ConnectedToSomeButNotAll ==
    \E t \in Nodes : t \in Succ[Root] /\ t \notin Succ[Nodes]

LimitedSeq ==
    [Seq -> FiniteSeq]

====