---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachable, ReachableAlgs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"working", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "working"

Expand(n) ==
  /\ pc = "working"
  /\ n \in marked
  /\ \E m \in Nodes :
       /\ m \notin marked
       /\ m \notin frontier
       /\ Edge(n, m)
       /\ frontier' = frontier \cup {m}
  /\ UNCHANGED <<marked, pc>>

Mark(m) ==
  /\ pc = "working"
  /\ m \in frontier
  /\ marked' = marked \cup {m}
  /\ frontier' = frontier \ {m}
  /\ UNCHANGED pc

Finish ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Expand(n)
  \/ \E m \in Nodes : Mark(m)
  \/ Finish

Spec == Init /\ [][Next]_vars

Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : \A m \in Nodes : Edge(n, m) => (m \in marked \/ m \in frontier)

Invariant2 == marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Invariant3 == ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3

PROPERTIES == (pc = "done") => (marked = ReachableFrom({Root}))
====