---- MODULE ReachableProofs ----
EXTENDS ReachSeq, ReachLemmata

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "idle"

StepMark(v) ==
    /\ pc = "idle"
    /\ v \in marked
    /\ frontier = {}
    /\ \E w \in Nodes : frontier' = {w}
    /\ pc' = "step"
    /\ UNCHANGED marked

StepFrontier ==
    /\ pc = "step"
    /\ frontier # {}
    /\ marked' = marked \cup frontier
    /\ frontier' = {}
    /\ pc' = "idle"

Finished ==
    /\ \A v \in Nodes : v \in marked => Succ[v] \subseteq (marked \cup frontier)

Next ==
    \/ \E v \in Nodes : StepMark(v)
    \/ StepFrontier
    \/ (Finished /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "step"}

Invariance1 ==
    /\ TypeOK
    /\ \A v \in marked : Succ[v] \subseteq (marked \cup frontier)

Invariance2 ==
    marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

Invariance3 ==
    Reachable(Root) = marked \cup Reachable(frontier)

PartialCorrectness ==
    Finished => (marked = Reachable(Root))

INVARIANTS == Invariance1 /\ Invariance2 /\ Invariance3
PROPERTIES == PartialCorrectness
====