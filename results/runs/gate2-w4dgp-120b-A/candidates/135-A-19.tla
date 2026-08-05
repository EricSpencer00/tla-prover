---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences, Reachable

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"init", "searching", "completed"}

Inv1 ==
    \A x \in frontier : \E y \in marked : x \in Succ[y]

Inv2 ==
    \A x \in marked : x # Root => \E y \in marked : x \in Succ[y]

Inv3 ==
    \A x \in Nodes : x \in marked <=> (Root = x \/ \E y \in marked : x \in Succ[y])

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "init"

SearchStep ==
    /\ pc = "searching"
    /\ frontier # {}
    /\ \E x \in frontier :
        /\ marked' = marked \cup {x}
        /\ frontier' = (frontier \ {x}) \cup Succ[x]
    /\ UNCHANGED pc

CompleteStep ==
    /\ pc = "searching"
    /\ frontier = {}
    /\ pc' = "completed"
    /\ UNCHANGED <<marked, frontier>>

InitStep ==
    /\ pc = "init"
    /\ pc' = "searching"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ InitStep
    \/ SearchStep
    \/ CompleteStep

Spec == Init /\ [][Next]_vars

PartialCorrectness ==
    \A x \in Nodes : (x \in marked /\ x # Root) => \E y \in marked : x \in Succ[y]

Termination == <>(pc = "completed")

ConnectedToSomeButNotAll == Succ

LimitedSeq == Seq

====