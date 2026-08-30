---- MODULE ReachableProofs ----
EXTENDS MisraSeq, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "working", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "idle"

Mark(v) ==
    /\ pc = "idle"
    /\ v \in frontier
    /\ marked' = marked \cup {v}
    /\ frontier' = frontier \ {v}
    /\ pc' = "working"

Explore(w) ==
    /\ pc = "working"
    /\ w \in frontier
    /\ frontier' = (frontier \cup {w}) \ marked
    /\ pc' = "idle"
    /\ UNCHANGED marked

Finish ==
    /\ frontier = {}
    /\ pc = "idle"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E v \in Nodes : Mark(v)
    \/ \E w \in Nodes : Explore(w)
    \/ Finish

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

Invariant1 ==
    / TypeOK
    /\ \A v \in marked : Successors(v) \subseteq (marked \cup frontier)

Invariant2 ==
    / Labeled1
    /\ (marked \cup frontier) \subseteq ReachableFrom(Root)
    /\ ReachableFrom(Root) \subseteq (marked \cup ReachableFrom(frontier))

Invariant3 ==
    / ReachableFrom(frontier) = ReachableFrom(frontier \cup marked)
    /\ ReachableFrom({}) = {}
    /\ ReachableFrom(Root) = (marked \cup ReachableFrom(frontier))

PartialCorrectness ==
    /\ pc = "done"
    /\ ReachableFrom(Root) = marked

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3
PROPERTIES == PartialCorrectness
====