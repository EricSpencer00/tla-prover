---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "running"

Step(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
  /\ marked' = marked \cup Succ[n]
  /\ pc' = IF marked = Nodes THEN "done" ELSE pc

Idle ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Step(n)
  \/ Idle

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Inv1 ==
  \A a \in frontier : \A b \in Succ[a] : b \in marked

Inv2 ==
  \A x \in marked : (x = Root) \/ (\E a \in marked : x \in Succ[a])

Inv3 ==
  \A x \in Nodes : (\A a \in marked : x \notin Succ[a]) => x \notin marked

PartialCorrectness ==
  marked = Nodes

Termination == <>(pc = "done")

ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq == [n \in Nat |-> IF n <= Cardinality(Nodes) THEN n ELSE 0]

====