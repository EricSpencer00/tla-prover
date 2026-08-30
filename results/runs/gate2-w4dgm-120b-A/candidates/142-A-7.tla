---- MODULE ReachableProofs ----
EXTENDS ReachAlgo, ReachableLemmas

CONSTANTS Nodes, Root

ASSUME Root \notin Nodes

VARIABLES mark, frontier, pc
vars == <<mark, frontier, pc>>

Init ==
  /\ mark = {}
  /\ frontier = {Root}
  /\ pc = "active"

Expand(n) ==
  /\ pc = "active"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ mark' = mark \cup {n}
  /\ pc' = "active"

ActivateSuccessor(n, m) ==
  /\ pc = "active"
  /\ n \in mark
  /\ m \notin mark
  /\ m \notin frontier
  /\ m \notin Nodes
  /\ frontier' = frontier \cup {m}
  /\ pc' = "active"

Stop ==
  /\ pc = "active"
  /\ frontier = {}
  /\ pc' = "stopped"
  /\ frontier' = frontier
  /\ mark' = mark

NEXT ==
  \/ \E n \in Nodes : Expand(n)
  \/ \E n \in Nodes, m \in Nodes : ActivateSuccessor(n, m)
  \/ Stop

Spec == Init /\ [][NEXT]_vars

TypeOK ==
  /\ mark \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"active", "stopped"}

Invariant1 ==
  TypeOK /\ (mark \cup frontier) = ReachableFrom({Root}, Nodes)

Invariant2 ==
  (mark \cup frontier) \cup ReachableFrom(frontier, Nodes) = ReachableFrom(mark \cup frontier, Nodes)

Invariant3 ==
  ReachableFrom({Root}, Nodes) = (mark \cup ReachableFrom(frontier, Nodes))

Invariants == Invariant1 /\ Invariant2 /\ Invariant3

Terminated ==
  pc = "stopped" => ReachableFrom({Root}, Nodes) = mark
====