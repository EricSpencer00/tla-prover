---- MODULE ReachableProofs ----
EXTENDS ReachableAlgorithm, ReachableLemmas, FiniteSets

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == << marked, frontier, pc >>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "active"

Advance(n) ==
  /\ pc = "active"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ marked' = marked \cup {n}
  /\ pc' = IF frontier = {n} THEN "done" ELSE "active"

Idle ==
  /\ pc = "active"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED << marked, frontier >>

Halt ==
  / pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ \E n \in Nodes : Advance(n)
  \/ Idle
  \/ Halt

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"active", "done"}
  /\ \A n \in marked : \A m \in Nodes : (n, m) \in Edges => (m \in marked \/ m \in frontier)

Invariant1 == TypeOK /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

Invariant2 == (marked \cup frontier) = ReachableFrom(marked)

Invariant3 == ReachableFrom({Root}) = (marked \cup frontier)

PartialCorrectness ==
  (pc = "done") => (marked = ReachableFrom({Root}))
====