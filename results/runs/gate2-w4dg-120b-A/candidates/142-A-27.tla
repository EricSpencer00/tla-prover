---- MODULE ReachableProofs ----
EXTENDS Integers, FiniteSets, ReachableDefs, GraphLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "run"

Step ==
    /\ pc = "run"
    /\ \E n \in Nodes, m \in Nodes :
         /\ n \in marked
         /\ m \notin marked
         /\ m \notin frontier
         /\ Succ(n, m)
         /\ frontier' = frontier \cup {m}
    /\ UNCHANGED <<marked, pc>>

MarkNode ==
    /\ frontier # {}
    /\ \E n \in frontier :
         /\ marked' = marked \cup {n}
         /\ frontier' = frontier \ {n}
    /\ UNCHANGED pc

Terminate ==
    /\ frontier = {}
    /\ pc = "run"
    /\ PC' = "halt"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ Step
    \/ MarkNode
    \/ Terminate

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "halt"}

FrontierContained ==
    \A n \in marked : \A m \in Nodes : Succ(n, m) => (m \in marked \/ m \in frontier)

BorderInvariant ==
    \A n \in Nodes : n \in Reachable(marked \cup frontier) <=> n \in marked \/ n \in Reachable(frontier)

ReachableInvariant ==
    Reachable(Root) = marked \cup Reachable(frontier)

PartialCorrectness ==
    (pc = "halt") => (marked = Reachable(Root))

====