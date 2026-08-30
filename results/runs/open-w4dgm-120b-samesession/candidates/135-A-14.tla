---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "exploring", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "idle"

Explore ==
    /\ frontier # {}
    /\ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \cup Succ[n]) \ marked
    /\ pc' = "exploring"

Terminate ==
    /\ frontier = {}
    /\ pc' \in {"idle", "exploring"}
    /\ pc # "done"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Terminate)

Inv1 == frontier \subseteq Nodes \ marked
Inv2 == marked \subseteq (Marked \cup Succ[Marked])
Inv3 == reachable(Root) = marked
PartialCorrectness == Root \in marked

Termination == []<>(pc = "done")

ConnectedToSomeButNotAll == Succ
LimitedSeq == Seq
====