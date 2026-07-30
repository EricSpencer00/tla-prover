---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ, ConnectedToSomeButNotAll

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

OverlapFrontier ==
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup frontier)
    /\ (marked \cup frontier) \subseteq Nodes

ReachableFromSet(S) ==
    LET Rec(S) ==
        \E n \in S : Rec(S \cup Succ[n]) \/ {n}
    IN Rec(S)

Inv1 == ReachableFromSet(marked) \cup frontier = ReachableFromSet(Nodes)

Inv2 ==
    /\ ReachableFromSet(Root) \subseteq marked \cup ReachableFromSet(frontier)
    /\ ReachableFromSet(Root) \supseteq marked \cup ReachableFromSet(frontier)

PartialCorrectness == ReachableFromSet(Root) = marked

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

ExploreMarked ==
    /\ \E n \in frontier :
         /\ n \notin marked
         /\ marked' = marked \cup {n}
         /\ frontier' = frontier \cup Succ[n]
    /\ UNCHANGED pc

ExploreSeen ==
    /\ \E n \in frontier :
         /\ n \in marked
         /\ frontier' = frontier \ {n}
    /\ UNCHANGED <<marked, pc>>

Terminate ==
    /\ frontier = {}
    /\ pc = "running"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ ExploreMarked
    \/ ExploreSeen
    \/ Terminate

Spec == Init /\ [][Next]_vars

Termination == (pc = "running") ~> (pc = "done")

LimitedSeq(n) == RecSeq(n)
RecSeq(n) ==
    IF n = 0 THEN << >>
    ELSE LET s == RecSeq(n - 1) IN s \cup << n >>

====