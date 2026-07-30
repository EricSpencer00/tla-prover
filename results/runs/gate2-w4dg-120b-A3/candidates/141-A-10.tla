---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

Null == 0

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore(n) ==
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \cup Succ[n]
  /\ pc' = pc

Drop(n) ==
  /\ n \in frontier
  /\ n \in marked
  /\ frontier' = frontier \ {n}
  /\ marked' = marked
  /\ pc' = pc

Next ==
  \/ \E n \in Nodes : Explore(n)
  \/ \E n \in Nodes : Drop(n)
  \/ /\ frontier = {}
     /\ pc' = "done"
     /\ marked' = marked
     /\ frontier' = frontier

Spec == Init /\ [][Next]_vars

Inv1 ==
  \A x \in marked : (Succ[x] \subseteq marked) \/ (Succ[x] \cap frontier # {})

Inv2 ==
  (marked \cup frontier)^+ = marked \cup frontier

Inv3 ==
  (Succ[Root] \cup marked) \cup frontier = Nodes

PartialCorrectness ==
  /\ frontier = {}
  /\ marked = Nodes

Termination ==
  /\ Cardinality(Nodes) < Cardinality(Nodes) + 1
  /\ (pc = "running") ~> (pc = "done")

LimitedSeq == Seq

Succ == ConnectedToSomeButNotAll

====