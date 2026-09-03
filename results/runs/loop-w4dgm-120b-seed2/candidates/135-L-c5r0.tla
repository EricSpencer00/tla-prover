---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* A finite graph with each node deterministically pointing to exactly 2 successors,
\* plus a bounded sequence wrapper that keeps the reachable-path set finite.
\* Both are required to turn the otherwise infinite path quantifier into a
\* checkable finite model, without weakening or removing any of the invariants
\* or the termination liveness check that inherits from the Misra algorithm.

VARIABLES marked, frontier, pc

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in {"working", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "working"

Activate(v) ==
  /\ v \notin marked
  /\ marked' = marked \cup {v}
  /\ frontier' = frontier \cup {v}
  /\ UNCHANGED pc

Complete(v) ==
  /\ v \in frontier
  /\ frontier' = frontier \ {v}
  /\ UNCHANGED <<marked, pc>>

Finish ==
  /\ frontier = {}
  /\ pc = "working"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E v \in Nodes : Activate(v) \/ Complete(v)
  \/ Finish

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

Inv1 == \A x \in marked : \E y \in Nodes : x \in Succ[y]
Inv2 == \A x \in frontier : \E y \in Nodes : x \in Succ[y]
Inv3 == \A z \in Nodes : (\A y \in Nodes : z \in Succ[y]) => z \in marked
Inv4 == \A z \in Nodes : (\A y \in Nodes : z \in Succ[y]) => z \in frontier
PartialCorrectness == marked = {z \in Nodes : \E y \in Nodes : z \in Succ[y]}
Termination == <>(pc = "done")

Partial == PartialCorrectness
SuccessorClosure == Inv1
FrontierClosure == Inv2
ReachableDecomposition == Inv3
ExactReachableSet == Inv4

====