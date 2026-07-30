---- MODULE MCReachable ----
EXTENDS Naturals

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "exploring"

StepExplore(n) ==
  /\ pc = "exploring"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \cup (Succ[n] \ marked)
  /\ pc' = "exploring"

StepComplete ==
  /\ pc = "exploring"
  /\ frontier = {}
  /\ pc' = "completed"
  /\ UNCHANGED <<marked, frontier>>

StepStall ==
  /\ pc = "completed"
  /\ UNCHANGED vars

Next ==
  \/ \E n \in Nodes : StepExplore(n)
  \/ StepComplete
  \/ StepStall

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"exploring", "completed"}

Inv1 ==
  frontier \subseteq (UNION {Succ[n] : n \in marked})

Inv2 ==
  \A n \in marked : (n = Root \/ Cardinality({m \in marked : n \in Succ[m]}) >= 1)

Inv3 ==
  \A n \in Nodes : (n \in marked) <=> (n = Root \/ Cardinality({m \in marked : n \in Succ[m]}) >= 1)

PartialCorrectness ==
  Root \in marked

Termination ==
  (pc = "completed") ~> (pc = "completed")

====