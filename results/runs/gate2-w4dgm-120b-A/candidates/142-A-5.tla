---- MODULE ReachableProofs ----
EXTENDS Reachable, Reaches

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "exploring"}

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "idle"

MarkFrontier ==
    /\ pc = "idle"
    /\ frontier = {}
    /\ frontier' = {n \in Nodes : \E m \in marked : (m, n) \in Edges}
    /\ UNCHANGED <<marked, pc>>

Explore(n) ==
    /\ pc = "idle"
    /\ n \in frontier
    /\ marked' = marked \cup {n}
    /\ frontier' = frontier \ {n}
    /\ pc' = "exploring"

FinishExploring ==
    /\ pc = "exploring"
    /\ pc' = "idle"
    /\ UNCHANGED <<marked, frontier>>

AllExplored ==
    /\ frontier = {}
    /\ pc = "idle"
    /\ frontier' = {n \in Nodes : \E m \in marked : (m, n) \in Edges}
    /\ UNCHANGED <<marked, pc>>

Next ==
    \/ MarkFrontier
    \/ \E n \in Nodes : Explore(n)
    \/ FinishExploring
    \/ AllExplored

Spec == Init /\ [][Next]_vars

Invariant1 ==
    /\ TypeOK
    /\ \A m \in marked : \A n \in Nodes : (m, n) \in Edges => (n \in marked \/ n \in frontier)

Invariant2 == marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Invariant3 == ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3

PROPERTIES == ReachesComplete
====