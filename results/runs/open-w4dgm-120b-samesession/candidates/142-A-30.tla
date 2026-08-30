---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachableLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "search"

Explore(n) ==
    /\ pc = "search"
    /\ n \in marked
    /\ frontier' = frontier \cup {m \in Nodes : m \in Succ(n)}
    /\ pc' = "search"
    /\ UNCHANGED marked

MarkNode(m) ==
    /\ pc = "search"
    /\ m \in frontier
    /\ marked' = marked \cup {m}
    /\ frontier' = frontier \ {m}
    /\ pc' = "search"

Quit ==
    /\ pc = "search"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

ResetSearch ==
    /\ pc = "done"
    /\ pc' = "search"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E n \in Nodes : Explore(n)
    \/ \E m \in Nodes : MarkNode(m)
    \/ Quit
    \/ ResetSearch

Spec == Init /\ [][Next]_vars

Invariant1 ==
    /\ marked \cup frontier \subseteq Nodes
    /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

Invariant2 == marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Invariant3 == ReachableFrom({Root}) = (marked \cup ReachableFrom(frontier))

TypeOK == VarsOK
StateConstraint == TypeOK

PartialCorrectness == (pc = "done") => (marked = ReachableFrom({Root}))

====