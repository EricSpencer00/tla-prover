---- MODULE MCReachable ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"working", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "working"

Advance ==
    /\ pc = "working"
    /\ frontier # {}
    /\ frontier' = {}
    /\ marked' = marked \cup (Succ[frontier])
    /\ UNCHANGED pc

Complete ==
    /\ pc = "working"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Reset ==
    /\ pc = "done"
    /\ pc' = "working"
    /\ frontier' = marked
    /\ UNCHANGED marked

Next == Advance \/ Complete \/ Reset

Spec == Init /\ [][Next]_vars

Inv1 ==
    \A n \in frontier : n \notin marked

Inv2 ==
    \A n \in marked : (n = Root) \/ (\E m \in Nodes : n \in Succ[m])

Inv3 ==
    \A n \in Nodes : (n \in marked) <=> (\E p \in LimitedSeq(Nodes) :
        /\ Len(p) >= 1
        /\ p[1] = Root
        /\ p[Len(p)] = n
        /\ \A i \in 1..(Len(p) - 1) : p[i + 1] \in Succ[p[i]])

PartialCorrectness ==
    \A n \in Nodes : (n \in marked) <=> (\E m \in Nodes : n \in Succ[m] \/ n = Root)

Termination == <>(pc = "done")

ConnectedToSomeButNotAll ==
    { n \in Nodes : Cardinality(Succ[n]) < Cardinality(Nodes) }

LimitedSeq(n) == UNION { Seq(n) : k \in 1..Cardinality(n) }

=======