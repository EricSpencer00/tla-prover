---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "active"

Step(n) ==
  /\ pc = "active"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ marked' = marked \cup Succ[n]
  /\ frontier' = frontier' \cup Succ[n]
  /\ pc' = IF marked \cup Succ[n] = Nodes THEN "done" ELSE pc

Next ==
  \/ \E n \in Nodes : Step(n)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"active", "done"}

Inv1 ==
  \A n \in frontier : n \in Nodes

Inv2 ==
  marked = {n \in Nodes : (\E m \in Nodes : m \in frontier /\ n \in Succ[m]) \/ n \in frontier}

Inv3 ==
  frontier \cap {n \in Nodes : (\E m \in Nodes : m \in frontier /\ n \in Succ[m])} = {}

PartialCorrectness ==
  \A n \in marked : (\E m \in Nodes : n \in Succ[m] \/ n = Root)

Termination ==
  \A n \in Nodes : (n \in frontier) ~> (n \notin frontier)

ConnectedToSomeButNotAll == Succ

LimitedSeq(S) == CHOOSE s \in S : TRUE

====