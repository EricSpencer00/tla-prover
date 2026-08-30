---- MODULE ReachableProofs ----
EXTENDS Integers, Reachable, ReachableLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"bfs", "halt"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "bfs"

Traverse(n) ==
  /\ pc = "bfs"
  /\ n \in marked
  /\ frontier' = frontier \cup Succ(n)
  /\ UNCHANGED <<marked, pc>>

Mark(n) ==
  /\ pc = "bfs"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

Halts ==
  /\ pc = "bfs"
  /\ frontier = {}
  /\ pc' = "halt"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Traverse(n)
  \/ \E n \in Nodes : Mark(n)
  \/ Halts

Spec == Init /\ [][Next]_vars

MarkFrontierSubset == frontier \subseteq marked \cup frontier

Invariants == {TypeOK, MarkFrontierSubset}

PartialCorrectness ==
  /\ pc = "halt"
  /\ marked = ReachableSet(Root)
====