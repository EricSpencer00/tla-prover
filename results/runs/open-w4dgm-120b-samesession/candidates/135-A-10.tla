---- MODULE MCReachable ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

SuccN == Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "checking", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "idle"

StartCheck ==
    /\ pc = "idle"
    /\ pc' = "checking"
    /\ frontier' = SuccN(Root)
    /\ UNCHANGED marked

CheckNode(n) ==
    /\ pc = "checking"
    /\ n \in frontier
    /\ marked' = marked \cup {n}
    /\ frontier' = (frontier \ {n}) \cup SuccN(n)
    /\ UNCHANGED pc

MarkDone ==
    /\ pc = "checking"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ StartCheck
    \/ \E n \in Nodes : CheckNode(n)
    \/ MarkDone
    \/ Done

Spec == Init /\ [][Next]_vars

Inv1 == frontier \subseteq (Nodes \ marked)
Inv2 == marked \cup frontier = Nodes
Inv3 == marked \cap frontier = {}
Reachable == marked = Nodes
PartialCorrectness == Reachable /\ (pc = "done")

Termination == <>(pc = "done")

LimitedSeq == Seq

ConnectedToSomeButNotAll == SuccN

====