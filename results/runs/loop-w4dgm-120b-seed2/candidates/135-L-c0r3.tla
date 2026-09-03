---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "working", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "idle"

Start ==
    /\ pc = "idle"
    /\ pc' = "working"
    /\ UNCHANGED <<marked, frontier>>

Mark(n) ==
    /\ pc = "working"
    /\ n \in frontier
    /\ marked' = marked \cup {n}
    /\ frontier' = (frontier \ {n}) \cup Succ[n]
    /\ UNCHANGED pc

Stop ==
    /\ pc = "working"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ Start
    \/ \E n \in Nodes : Mark(n)
    \/ Stop

Spec == Init /\ [][Next]_vars

Inv1 == frontier \subseteq marked
Inv2 == marked \cap frontier = {}
Inv3 == marked \cup frontier = Nodes
PartialCorrectness == Root \in marked

Termination == <>(pc = "done")

ConnectedToSomeButNotAll == Succ

LimitedSeq(s) == Seq(s)

====