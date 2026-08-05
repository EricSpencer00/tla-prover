---- MODULE ReachableProofs ----
EXTENDS Integers, Reachability

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

NoReach == ReachFrom(Nodes, frontier, {})

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"searching", "done"}
  /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

Init ==
  /\ marked = {Root}
  /\ frontier = Succ(Root)
  /\ pc = "searching"

Expand ==
  /\ frontier # {}
  /\ \E x \in frontier :
       /\ marked' = marked \cup {x}
       /\ frontier' = (frontier \ {x}) \cup Succ(x)
  /\ pc' = pc

EmptyFrontier ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Expand \/ EmptyFrontier

Spec == Init /\ [][Next]_vars

Inv1 == TypeOK

Inv2 == marked \cup ReachFrom(Nodes, frontier, marked) = ReachFrom(Nodes, marked \cup frontier, {})

Inv3 == ReachFrom(Nodes, {Root}, {}) = marked \cup ReachFrom(Nodes, frontier, marked)

TerminationOK == (pc = "done") ~> (marked = ReachFrom(Nodes, {Root}, {}))

====