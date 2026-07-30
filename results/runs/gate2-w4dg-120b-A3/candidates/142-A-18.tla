---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachabilityLemmas

CONSTANTS Nodes, Root

ASSUME Nodes = {0, 1, 2}

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"init", "searching", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "init"

Expand ==
    /\ pc \in {"init", "searching"}
    /\ frontier # {}
    /\ frontier' = {w \in Nodes : \E v \in frontier : w \in Succ(v)}
    /\ marked' = marked \cup frontier
    /\ pc' = IF frontier \subseteq {w \in Nodes : \E v \in marked : w \in Succ(v)} THEN "done" ELSE "searching"

Spec == Init /\ [][Expand]_vars

Invariant1 ==
    /\ TypeOK
    /\ \A v \in marked : Succ(v) \subseteq (marked \cup frontier)

Invariant2 ==
    /\ marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Invariant3 ==
    /\ ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

Theorem PartialCorrectness == (\A v \in Nodes : v \in marked) ~> (\A v \in Nodes : v \in ReachableFrom({Root}))

====