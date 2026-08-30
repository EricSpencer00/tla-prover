---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "active", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = Succ(Root)
    /\ pc = "active"

MarkStep ==
    /\ pc = "active"
    /\ frontier # {}
    /\ marked' = marked \cup frontier
    /\ frontier' = {n \in Nodes : \E m \in frontier : n \in Succ(m)} \ marked
    /\ pc' = IF frontier' = {} THEN "done" ELSE "active"

Done ==
    /\ pc = "active"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED << marked, frontier >>

Next == MarkStep \/ Done

Spec == Init /\ [][Next]_vars

Inv1 == frontier \subseteq Nodes \ marked
Inv2 == marked \cup frontier = Nodes
Inv3 == \A a, b \in marked : (a \in Succ(b) \/ b \in Succ(a)) \/ a = b
PartialCorrectness == marked = Nodes

Termination == <>(pc = "done")

ConnectedToSomeButNotAll(n) == Succ(n)

LimitedSeq(S) == S

====