---- MODULE ReachableProofs ----
EXTENDS SequentialReaches, ReachesProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "idle"

Mark(n) ==
    /\ pc = "idle"
    /\ n \in marked
    /\ \E s \in Nodes : s \notin marked /\ s \notin frontier /\ <<n, s>> \in Edges
    /\ frontier' = frontier \cup {n}
    /\ pc' = "idle"
    /\ UNCHANGED marked

Commit(n) ==
    /\ pc = "idle"
    /\ n \in frontier
    /\ marked' = marked \cup {n}
    /\ frontier' = frontier \ {n}
    /\ pc' = "idle"

Cancel(n) ==
    /\ pc = "idle"
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ pc' = "idle"

Quiesce ==
    /\ pc = "idle"
    /\ \A n \in Nodes : n \notin frontier => \A s \in Nodes : <<n, s>> \notin Edges \/ s \in marked
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E n \in Nodes : Mark(n) \/ Commit(n) \/ Cancel(n)
    \/ Quiesce

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "done"}

Invariant1 ==
    /\ TypeOK
    /\ \A n \in marked : \A s \in Nodes : <<n, s>> \in Edges => s \in marked \/ s \in frontier

Invariant2 ==
    /\ TypeOK
    /\ marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Invariant3 ==
    /\ TypeOK
    /\ ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3

PartialCorrectness ==
    (pc = "done") => (marked = ReachableFrom({Root}))
====