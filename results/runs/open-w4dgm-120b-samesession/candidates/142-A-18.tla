---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachable, ReachableAlgs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

TypeOK == marked \subseteq Nodes /\ frontier \subseteq Nodes /\ pc \in {"init", "idle"}

Init == marked = {} /\ frontier = {Root} /\ pc = "init"

MarkStep == pc = "init" /\ \E n \in frontier : marked' = marked \cup {n} /\ frontier' = frontier \ {n} /\ pc' = "idle"
TraverseStep == pc = "idle" /\ \E m \in Nodes :
    /\ m \notin marked
    /\ \E n \in marked : GraphEdge(n, m)
    /\ frontier' = frontier \cup {m} /\ pc' = "init" /\ UNCHANGED marked
Stall == \A m \in Nodes : m \in marked \/ m \notin frontier => ~GraphEdge(Root, m) /\ UNCHANGED <<marked, frontier, pc>>

Next == MarkStep \/ TraverseStep \/ Stall

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

Invariant1 == TypeOK /\ (\A n \in marked : \A m \in Nodes : GraphEdge(n, m) => (m \in marked \/ m \in frontier))
Invariant2 == marked \cup ReachableFrom(frontier, Nodes) = ReachableFrom(marked \cup frontier, Nodes)
Invariant3 == ReachableFrom(Root, Nodes) = marked \cup ReachableFrom(frontier, Nodes)

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3

TerminationResult == ReachableFrom(Root, Nodes) = marked

PROPERTIES == TerminationResult
====