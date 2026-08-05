---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, GraphReachability

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"exploring", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "exploring"

Explore(n) ==
    /\ n \in frontier
    /\ \E m \in Nodes :
        /\ n \in marked \cup frontier
        /\ succ[n, m]
        /\ m \notin marked
        /\ m \notin frontier
        /\ frontier' = (frontier \ {n}) \cup {m}
    /\ UNCHANGED <<marked, pc>>

Mark(n) ==
    /\ n \in frontier
    /\ marked' = marked \cup {n}
    /\ frontier' = frontier \ {n}
    /\ UNCHANGED pc

Terminate ==
    /\ frontier = {}
    /\ \A n \in Nodes : \A m \in Nodes : ~succ[n, m]
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

InitExplore == \E n \in Nodes : Explore(n)

Next == InitExplore \/ \E n \in Nodes : Mark(n) \/ Terminate

Spec == Init /\ [][Next]_vars

Invariant1 ==
    /\ TypeOK
    /\ \A n \in marked : \A m \in Nodes : succ[n, m] => (m \in marked \/ m \in frontier)

Invariant2 ==
    ReachFC(marked) \cup ReachFC(frontier) = ReachFC(marked \cup frontier)

Invariant3 ==
    ReachFC(Root) = marked \cup ReachFC(frontier)

SpecTermination == Spec /\ (pc = "done") => (marked = ReachFC(Root))

====