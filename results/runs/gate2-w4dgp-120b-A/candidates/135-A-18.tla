---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = 0

Mark(n) ==
  /\ pc = 0
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \cup (Succ[n] \ marked)
  /\ pc' = 0

Quit ==
  /\ pc = 0
  /\ frontier = {}
  /\ pc' = 1
  /\ UNCHANGED <<marked, frontier>>

Next == (\E n \in Nodes : Mark(n)) \/ Quit

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in 0..1

Inv1 ==
  \A n \in marked : \A m \in Succ[n] : m \in marked \/ m \in frontier

Inv2 ==
  \A n \in frontier : \A m \in Succ[n] : m \in marked \/ m \in frontier

Inv3 ==
  marked \cup frontier = Nodes

PartialCorrectness ==
  frontier = {} => marked = Nodes

Termination ==
  <>(pc = 1)
====