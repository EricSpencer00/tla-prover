---- MODULE ReachableProofs ----
EXTENDS ReachableSeq, ReachableLemmas

CONSTANTS Nodes, Root

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "idle"

Mark(v) ==
  /\ pc = "idle"
  /\ v \in frontier
  /\ marked' = marked \cup {v}
  /\ frontier' = frontier \ {v}
  /\ pc' = "inMove"

Expand(v, w) ==
  /\ pc = "inMove"
  /\ v \in marked
  /\ w \in Next(v)
  /\ w \notin marked
  /\ w \notin frontier
  /\ frontier' = frontier \cup {w}
  /\ pc' = "idle"
  /\ marked' = marked

Finish ==
  /\ frontier = {}
  /\ marked = Nodes
  /\ pc' = pc
  /\ frontier' = frontier
  /\ marked' = marked

Next ==
  \/ Finish
  \/ \E v \in Nodes : Mark(v)
  \/ \E v \in Nodes, w \in Nodes : Expand(v, w)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "inMove"}
  /\ \A v \in marked : (Neighbors(v) \subseteq Nodes)

Invariant1 ==
  /\ TypeOK
  /\ \A v \in marked : Neighbors(v) \subseteq (marked \cup frontier)

Invariant2 == marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

Invariant3 == Reachable(Nodes) = marked \cup Reachable(frontier)

PartialCorrectness ==
  (frontier = {}) => (marked = Reachable(Nodes))

StateSpaceBound == \E v \in Nodes : Expand(v, v)

LivenessReachesQuiescence == (frontier # {}) ~> (frontier = {})

INVARIANTS == TypeOK /\ Invariant1 /\ Invariant2 /\ Invariant3
PROPERTIES == PartialCorrectness
====