---------------------------- MODULE MCReachable ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES mark, frontier, pc

vars == <<mark, frontier, pc>>

RECURSIVE SumOver(_)
SumOver(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN x + SumOver(S \ {x})

TypeOK ==
    /\ mark \in [Nodes -> 0..3]
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "working", "done"}

Init ==
    /\ mark = [n \in Nodes |-> IF n = Root THEN 3 ELSE 0]
    /\ frontier = {Root}
    /\ pc = "idle"

Explore(n) ==
    /\ pc = "idle"
    /\ n \in frontier
    /\ mark[n] # 2
    /\ mark' = [mark EXCEPT ![n] = mark[n] + 1]
    /\ frontier' = frontier \cup Succ[n]
    /\ pc' = "working"

Acknowledge(n) ==
    /\ pc = "working"
    /\ mark[n] = 3
    /\ pc' = "idle"
    /\ UNCHANGED <<mark, frontier>>

Finish ==
    /\ pc \in {"idle", "working"}
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<mark, frontier>>

CongestionSpill(n) ==
    /\ pc = "working"
    /\ mark[n] \in 1..2
    /\ mark' = [mark EXCEPT ![n] = mark[n] + 1]
    /\ UNCHANGED <<frontier, pc>>

Next ==
    \/ \E n \in Nodes : Explore(n)
    \/ \E n \in Nodes : Acknowledge(n)
    \/ Finish
    \/ \E n \in Nodes : CongestionSpill(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Finish)

Inv1 == \A n \in Nodes : mark[n] >= 1 => n \in frontier

Inv2 == frontier \subseteq (ConnectedToSomeButNotAll \cup {Root})

Inv3 == \A n \in Nodes : mark[n] = 3 => n \in ConnectedToSomeButNotAll

PartialCorrectness == \A n \in Nodes : mark[n] = 3 => n \in Succ[Root]

Termination == <>(pc = "done")

ConnectedToSomeButNotAll ==
    {n \in Nodes : \E m \in Nodes : n \in Succ[m] /\ n # m}

LimitedSeq(S) == Sequence(S)
=============================================================================