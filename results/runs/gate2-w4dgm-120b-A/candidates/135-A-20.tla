---------------------------- MODULE MCReachable ----------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"working", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = Succ(Root)
    /\ pc = "working"

Step ==
    /\ pc = "working"
    /\ frontier # {}
    /\ marked' = marked \cup frontier
    /\ frontier' = {y \in Nodes : \E x \in frontier : y \in Succ(x)} \ marked
    /\ pc' = IF frontier' = {} THEN "done" ELSE "working"

Next == Step

Spec == Init /\ [][Next]_vars

Inv1 ==
    \A x \in frontier : \E y \in marked : x \in Succ(y)

Inv2 ==
    \A x \in marked : (\A y \in Nodes : y \in Succ(x) => y \in marked \cup frontier) \/ x = Root

Inv3 ==
    \A x \in Nodes : (x \in marked \/ x \in frontier) <=> (x = Root \/ \E y \in Nodes : x \in Succ(y))

PartialCorrectness ==
    \A x \in Nodes : (x \in marked \/ x \in frontier) <=> (x = Root \/ \E y \in Nodes : x \in Succ(y))

Termination ==
    (pc = "working") ~> (pc = "done")

LimitedSeq(S) == S

ConnectedToSomeButNotAll(x) == Succ(x)

=============================================================================