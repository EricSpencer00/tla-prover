---- MODULE ReachableProofs ----
EXTENDS GraphSets, ReachabilityProofs, NaturalNumbers

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"working", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "working"

MarkStep(n) ==
  /\ pc = "working"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ pc' = pc

AddSuccessorStep(n, m) ==
  /\ pc = "working"
  /\ n \in marked
  /\ m \in Succ(n)
  /\ m \notin marked
  /\ m \notin frontier
  /\ frontier' = frontier \cup {m}
  /\ pc' = pc
  /\ marked' = marked

Terminate ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = "done"
  /\ marked' = marked
  /\ frontier' = frontier

Next ==
  \/ \E n \in Nodes : MarkStep(n)
  \/ \E n \in Nodes, m \in Nodes : AddSuccessorStep(n, m)
  \/ Terminate

Spec == Init /\ [][Next]_vars

Invariant1 ==
  TypeOK /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

Invariant2 == marked \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

Invariant3 == ReachFrom({Root}) = (marked \cup ReachFrom(frontier))

PartialCorrectness == pc = "done" => marked = ReachFrom({Root})

====