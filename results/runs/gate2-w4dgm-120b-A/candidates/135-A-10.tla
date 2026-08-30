---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "searching"

Mark(n) ==
    /\ pc = "searching"
    /\ n \in frontier
    /\ n \notin marked
    /\ marked' = marked \cup {n}
    /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
    /\ pc' = "searching"

Backtrack ==
    /\ pc = "searching"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Idle ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : Mark(n)
    \/ Backtrack
    \/ Idle

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"searching", "done"}

Inv1 == frontier \subseteq (Nodes \ marked)

Inv2 ==
    \A n \in marked : \E m \in marked : n \in Succ[m]

Inv3 ==
    \A n \in Nodes : (n \in marked) <=> \E seq \in LimitedSeq(Nodes) :
        /\ seq[1] = Root
        /\ seq[Len(seq)] = n
        /\ \A i \in 1..(Len(seq) - 1) : seq[i + 1] \in Succ[seq[i]]

PartialCorrectness == reachableNodes \subseteq marked

Termination == (pc = "searching") ~> (pc = "done")

ConnectedToSomeButNotAll == Succ
LimitedSeq(S) == UNION {Sequences.Seq(f) : f \in [1..Cardinality(S) -> S]}
====