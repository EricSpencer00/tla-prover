---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachableLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Successors(n) == { m \in Nodes : {n, m} \in Edge }

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"searching", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = Successors(Root)
  /\ pc = "searching"

MarkNode(n) ==
  /\ pc = "searching"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = (frontier \cup Successors(n)) \ {n}
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "searching"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == \E n \in Nodes : MarkNode(n) \/ Terminate

Spec == Init /\ [][Next]_vars

Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : Successors(n) \subseteq (marked \cup frontier)

Invariant2 ==
  \A n \in marked : ReachableFrom(n, marked) = ReachableFrom(n, frontier)

Invariant3 ==
  ReachableFrom(Root, {}) \cup frontier = ReachableFrom(Root, marked)

PartialCorrectness ==
  /\ pc = "done"
  /\ marked = ReachableFrom(Root, {})

Initialize ==
  \E n \in Nodes : MarkNode(n)

Search ==
  /\ pc = "searching"
  /\ frontier # {}
  /\ Initialize

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

NextState == Search \/ Done

ReachableSpec == Spec /\ [][NextState]_vars

INVARIANTS == Invariant1

PROPERTIES == Invariant2 /\ Invariant3 /\ PartialCorrectness
====