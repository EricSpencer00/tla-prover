---- MODULE ReachableProofs ----
EXTENDS Naturals, ReachabilityAlgebra

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

RECURSIVE Reachable(_)
Reachable(S) ==
    IF S = {} THEN {}
    ELSE LET x == CHOOSE y \in S : TRUE IN {x} \cup Reachable(S \cup Succ(x))

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

FrontierCondition ==
    \A m \in marked, s \in Succ(m) : s \in marked \cup frontier

Init ==
    /\ marked = {Root}
    /\ frontier = Succ(Root)
    /\ pc = "running"

Step ==
    /\ pc = "running"
    /\ \E v \in frontier :
         /\ frontier' = (frontier \ {v}) \cup Succ(v)
         /\ marked' = marked \cup {v}
    /\ UNCHANGED pc

Idle ==
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED << marked, frontier >>

Halt ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Step \/ Idle \/ Halt

Spec == Init /\ [][Next]_vars

Invariant1 ==
    /\ TypeOK
    /\ FrontierCondition

Invariant2 ==
    Reachable(marked) \cup Reachable(frontier) = Reachable(marked \cup frontier)

Invariant3 ==
    Reachable(Root) = marked \cup Reachable(frontier)

PartialCorrectness ==
    /\ pc = "done"
    => marked = Reachable(Root)

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3

PROPERTIES == PartialCorrectness

====