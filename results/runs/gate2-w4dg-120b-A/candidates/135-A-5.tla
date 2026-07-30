---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {0, 1, 2}

Init ==
    /\ marked = {Root}
    /\ frontier = Succ[Root]
    /\ pc = 0

Step ==
    /\ frontier # {}
    /\ pc = 0
    /\ marked' = marked \cup frontier
    /\ frontier' = UNION { Succ[n] : n \in frontier }
    /\ pc' = IF (marked \cup frontier) = Nodes THEN 1 ELSE 0

Complete ==
    /\ frontier = {}
    /\ pc = 1
    /\ pc' = 2
    /\ UNCHANGED << marked, frontier >>

Next == Step \/ Complete

Spec == Init /\ [][Next]_vars

Inv1 ==
    \A n \in frontier : \A m \in Succ[n] : m \in marked

Inv2 ==
    \A n \in marked : n \in (IF frontier = {} THEN Nodes ELSE frontier)

Inv3 ==
    \A n \in Nodes :
        (n \in marked) <=> \E k \in 1..Len(Seq) : Seq[k] = n

PartialCorrectness ==
    \A n \in Nodes :
        (n \in marked) <=> (\E k \in 1..Len(Seq) : Seq[k] = n)

Termination == (pc = 2) ~> (pc = 2)

====