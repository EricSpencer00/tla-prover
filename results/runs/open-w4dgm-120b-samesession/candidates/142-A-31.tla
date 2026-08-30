---- MODULE ReachableProofs ----
EXTENDS Reachable, GraphLemmas

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

Explore ==
  /\ frontier # {}
  /\ \E n \in frontier:
       marked' = marked \cup {n}
       frontier' = (frontier \ {n}) \cup (Succ[n] \ (marked \cup frontier))
  /\ pc' = "working"

Terminate ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ marked' = marked
  /\ frontier' = frontier

Idle ==
  /\ pc = "done"
  /\ marked = Nodes
  /\ frontier = {}
  /\ marked' = marked
  /\ frontier' = frontier
  /\ pc' = pc

Next ==
  \/ Explore
  \/ Terminate
  \/ Idle

Spec == Init /\ [][Next]_vars

Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Invariant2 ==
  /\ marked \cup ReachFrom(marked \cup frontier) = ReachFrom(marked \cup frontier)

Invariant3 ==
  ReachFrom({Root}) = marked \cup ReachFrom(frontier)

PartialCorrectness ==
  (pc = "done") => (ReachFrom({Root}) = marked)

====