---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachableLemmas, Integers

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
    /\ pc = "exploring"
    /\ n \in marked
    /\ n \notin frontier
    /\ frontier' = frontier \cup {n}
    /\ UNCHANGED <<marked, pc>>

Mark(n) ==
    /\ pc = "exploring"
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ marked' = marked \cup {n}
    /\ UNCHANGED pc

Done ==
    /\ pc = "exploring"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E n \in Nodes : Explore(n)
    \/ \E n \in Nodes : Mark(n)
    \/ Done

Spec == Init /\ [][Next]_vars

Invariant1 ==
    /\ TypeOK
    /\ \A m \in marked : Succ(m) \subseteq (marked \cup frontier)

Invariant2 ==
    (marked \cup frontier) \cup Succ(marked \cup frontier) = ReachableFrom(Root)

Invariant3 ==
    ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

ReachableCorrect == (pc = "done") => (ReachableFrom(Root) = marked)
====