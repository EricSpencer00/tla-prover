---- MODULE ReachableProofs ----
EXTENDS Reaches, ReachesProofs, Naturals

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "working"

Advance ==
    /\ pc = "working"
    /\ frontier # {}
    /\ marked' = marked \cup frontier
    /\ frontier' = { m.succ : m \in marked \cup frontier, m.succ \notin marked \cup frontier }
    /\ pc' = IF (frontier \cup marked) = Nodes THEN "done" ELSE "working"

Finish ==
    /\ pc = "working"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Reset ==
    /\ pc = "done"
    /\ pc' = "working"
    /\ marked' = {}
    /\ frontier' = {Root}

Next == Advance \/ Finish \/ Reset

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"working", "done"}
    /\ \A m \in marked : \A t \in frontier : m # t

Inv1 == TypeOK /\ \A n \in marked : n.succ \in marked \cup frontier
Inv2 == ReachesFrom(Nodes, marked \cup frontier) = ReachesFrom(Nodes, marked) \cup ReachesFrom(Nodes, frontier)
Inv3 == ReachesFrom(Nodes, Root) = marked \cup ReachesFrom(Nodes, frontier)
StateBound == Cardinality(marked) + Cardinality(frontier) <= Cardinality(Nodes)

SpecOK == TypeOK /\ Inv1 /\ Inv2 /\ Inv3

PartialCorrectness == (pc = "done" /\ frontier = {}) => marked = ReachesFrom(Nodes, Root)

====