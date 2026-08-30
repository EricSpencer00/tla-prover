---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachability

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "working", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "init"

Search ==
  /\ pc \in {"init", "working"}
  /\ frontier # {}
  /\ marked' = marked \cup frontier
  /\ frontier' = {}
  /\ pc' = "working"

Expand(n) ==
  /\ pc \in {"init", "working"}
  /\ n \in marked
  /\ frontier' = frontier \cup ReachableFrom(n)
  /\ UNCHANGED <<marked, pc>>

Finalize ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Search
  \/ \E n \in Nodes: Expand(n)
  \/ Finalize

Spec == Init /\ [][Next]_vars

Invariant1 ==
  /\ TypeOK
  /\ (\A n \in Nodes: (n \in marked) => ReachableFrom(n) \subseteq (marked \cup frontier))

Invariant2 ==
  /\ TypeOK
  /\ (marked \cup ReachableFromSet(marked)) \cup ReachableFromSet(frontier)
       = ReachableFromSet(marked \cup frontier)

Invariant3 ==
  /\ TypeOK
  /\ ReachableFromSet({Root}) = marked \cup ReachableFromSet(frontier)

PartialCorrectness == (pc = "done") ~> (marked = ReachableFromSet({Root}))

INVARIANTS == {Invariant1, Invariant2, Invariant3}
PROPERTIES == {PartialCorrectness}
====