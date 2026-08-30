---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachableLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "working", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "idle"

Mark(n) ==
  /\ pc = "working"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ pc' = pc

Expand(n) ==
  /\ pc = "working"
  /\ n \in marked
  /\ frontier' = frontier \cup {m \in Nodes : m \in Succ(n) /\ m \notin marked}
  /\ pc' = pc
  /\ marked' = marked

Start ==
  /\ pc = "idle"
  /\ frontier # {}
  /\ pc' = "working"
  /\ marked' = marked
  /\ frontier' = frontier

Finish ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = "done"
  /\ marked' = marked
  /\ frontier' = frontier

Next ==
  \/ \E n \in Nodes : Mark(n)
  \/ \E n \in Nodes : Expand(n)
  \/ Start
  \/ Finish

Spec == Init /\ [][Next]_vars

Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

Invariant2 == marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Invariant3 == ReachableFrom({Root}) = (marked \cup ReachableFrom(frontier))

PartialCorrectness == (pc = "done") => (marked = ReachableFrom({Root}))

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3
PROPERTIES == PartialCorrectness
====