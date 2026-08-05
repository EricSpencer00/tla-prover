---- MODULE ReachableProofs ----
EXTENDS Naturals, ReachabilityAlgs, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in 0..2
  /\ \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = 0

Mark ==
  /\ pc = 0
  /\ frontier # {}
  /\ marked' = marked \cup frontier
  /\ frontier' = {}
  /\ pc' = 1

Explore ==
  /\ pc = 1
  /\ \E n \in marked \ frontier :
       frontier' = frontier \cup Succ[n]
  /\ pc' = 0
  /\ UNCHANGED marked

Finished ==
  /\ pc = 0
  /\ frontier = {}
  /\ pc' = 2
  /\ UNCHANGED <<marked, frontier>>

Next == Mark \/ Explore \/ Finished

Spec == Init /\ [][Next]_vars

Inv2 == (marked \cup ReachableFrom(frontier)) = ReachableFrom(marked \cup frontier)
Inv3 == ReachableFrom(Root) = (marked \cup ReachableFrom(frontier))
TypeInv == TypeOK

Properties ==
  /\ TypeInv
  /\ Inv2
  /\ Inv3
  /\ (pc = 2) ~> (marked = ReachableFrom(Root))
====