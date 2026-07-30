---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "halted"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Bump ==
  /\ Cardinality(Nodes) > 0
  /\ \E x \in frontier :
       \/ /\ x \notin marked
            /\ marked' = marked \cup {x}
            /\ frontier' = frontier \cup Succ[x]
       \/ /\ x \in marked
            /\ frontier' = frontier \ {x}
  /\ pc' = IF frontier' = {} THEN "halted" ELSE "running"

MarkedClosedUnderSuccessors ==
  \A x \in marked : \A y \in Succ[x] : y \in marked \/ frontier

ReachableFromFrontierIsCovered ==
  (marked \cup frontier) \cup {y \in Nodes : \E z \in frontier : y \in Succ[z]}
    = {y \in Nodes : \E z \in marked \cup frontier : y \in Succ[z]}

MarkedPlusFrontierReachesAll ==
  {y \in Nodes : \E z \in marked \cup frontier : y \in Succ[z]} = marked \cup frontier

PartialCorrectness == \A y \in Nodes : (y \in marked) <=> (\E x \in marked \cup frontier : y \in Succ[x])

Spec == Init /\ [][Bump]_vars

Termination == (\A y \in Nodes : y \in marked \/ \E z \in frontier : y \in Succ[z]) ~> (frontier = {})

ConnectedToSomeButNotAll == TRUE

LimitedSeq == Seq
====