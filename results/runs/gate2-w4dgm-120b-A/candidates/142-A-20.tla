---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachability

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "idle"

Mark(n) ==
    /\ pc = "idle"
    /\ n \in frontier
    /\ marked' = marked \cup {n}
    /\ frontier' = frontier \ {n}
    /\ pc' = "busy"

Expand(n) ==
    /\ pc = "busy"
    /\ n \in marked
    /\ frontier' = frontier \cup {m \in Nodes : m \notin marked /\ m \notin frontier}
    /\ pc' = "idle"
    /\ UNCHANGED marked

Halt ==
    /\ pc = "idle"
    /\ frontier = {}
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : Mark(n)
    \/ \E n \in Nodes : Expand(n)
    \/ Halt

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "busy"}
    /\ \A n \in marked : \A m \in Nodes : (m \in Succ(n) => (m \in marked \/ m \in frontier))

InductiveStep ==
    \A n \in marked : \A m \in Nodes : (m \in Succ(n) => (m \in marked \/ m \in frontier))

FrontierClosure ==
    ReachableFrom(marked \cup frontier) = ReachableFrom(marked) \cup ReachableFrom(frontier)

MarkedCompletesReachability ==
    ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

INVARIANTS == TypeOK /\ InductiveStep /\ FrontierClosure /\ MarkedCompletesReachability

Bounded == Cardinality(marked) <= 3

PROPERTIES == Bounded

====