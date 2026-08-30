---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"idle", "working", "done"}

Init == /\ marked = {Root}
        /\ frontier = {}
        /\ pc = "idle"

Expand(n) == /\ pc = "working"
             /\ frontier' = frontier \cup {n}
             /\ pc' = "idle"
             /\ UNCHANGED marked

Mark(n) == /\ pc = "idle"
           /\ n \in frontier
           /\ marked' = marked \cup {n}
           /\ frontier' = frontier \ {n}
           /\ pc' = "working"

Start == /\ pc = "idle"
         /\ \E n \in Nodes : n \in frontier
         /\ pc' = "working"
         /\ UNCHANGED <<marked, frontier>>

Done == /\ pc = "idle"
        /\ frontier = {}
        /\ pc' = "done"
        /\ UNCHANGED <<marked, frontier>>

Next == \/ \E n \in Nodes : Expand(n) \/ Mark(n)
        \/ Start \/ Done

Spec == Init /\ [][Next]_vars

FrontierLater == frontier \subseteq (Nodes \ marked)

FrontierMarks == Nodes \subseteq (FrontierLater \cup (Nodes \ frontier))

MarkedReaches == (Nodes \ marked) \subseteq (Nodes \ frontier)

ReachableEqualsMarked == Nodes = marked

Invariant1 == TypeOK /\ FrontierLater
Invariant2 == FrontierMarks
Invariant3 == MarkedReaches

Terminating == pc = "done"

ReachesAtTermination == Terminating => ReachableEqualsMarked

====