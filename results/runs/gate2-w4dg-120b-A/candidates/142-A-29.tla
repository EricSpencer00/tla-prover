---- MODULE ReachableProofs ----
EXTENDS Integers, Sequences, ReachableAlg, ReachableLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "searching", "done"}

InitReachableAlg ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"

ExploreFrontier ==
  /\ frontier # {}
  /\ pc # "done"
  /\ \E w \in frontier :
       frontier' = frontier \cup (Succ[w] \ marked)
  /\ pc' = "searching"
  /\ UNCHANGED marked

MarkNode ==
  /\ frontier # {}
  /\ \E w \in frontier :
       /\ marked' = marked \cup {w}
       /\ frontier' = frontier \ {w}
  /\ pc' = "searching"

Complete ==
  /\ frontier = {}
  /\ pc # "done"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Init == InitReachableAlg
Next == ExploreFrontier \/ MarkNode \/ Complete

Spec == Init /\ [][Next]_vars

Invariant1 ==
  /\ TypeOK
  /\ \A x \in marked : Succ[x] \subseteq (marked \cup frontier)

Invariant2 ==
  marked \cup ReachableFrom(Nodes, frontier) = ReachableFrom(Nodes, marked \cup frontier)

Invariant3 ==
  ReachableFrom(Nodes, {Root}) = marked \cup ReachableFrom(Nodes, frontier)

PartialCorrectness ==
  /\ pc = "done"
  => marked = ReachableFrom(Nodes, {Root})

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3

PROPERTIES == PartialCorrectness

====