---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Nodes, Root, Succ

StateSpace == {1, 2, 3, 4}

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq StateSpace
    /\ frontier \subseteq StateSpace
    /\ pc \in {"idle", "searching", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = Succ(Root)
    /\ pc = "idle"

Search ==
    /\ pc = "idle"
    /\ frontier # {}
    /\ pc' = "searching"
    /\ UNCHANGED <<marked, frontier>>

Expand(n) ==
    /\ pc = "searching"
    /\ n \in frontier
    /\ marked' = marked \cup {n}
    /\ frontier' = (frontier \cup Succ(n)) \ {n}
    /\ UNCHANGED pc

Complete ==
    /\ pc = "searching"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Quiesce ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ Quiesce
    \/ \E n \in StateSpace : Expand(n)
    \/ Search
    \/ Complete

Spec == Init /\ [][Next]_vars

SuccessorClosure ==
    /\ frontier \subseteq StateSpace
    /\ (Frontier \cap marked = {})
    /\ \A n \in frontier : \A m \in marked : n # m
    /\ \A n \in frontier : Succ(n) \subseteq (marked \cup frontier)

ReachableDecomposition ==
    \A n \in StateSpace :
        n \in marked => \E seq \in LimitedSeq(StateSpace) :
            /\ seq[1] = Root
            /\ seq[Len(seq)] = n
            /\ \A i \in 1 .. (Len(seq) - 1) : seq[i + 1] \in Succ(seq[i])

Inv1 == TypeOK
Inv2 == SuccessorClosure
Inv3 == ReachableDecomposition

PartialCorrectness ==
    (pc = "done") => (marked = StateSpace)

Termination ==
    \A n \in StateSpace : <>(n \in marked)

======