---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

FiniteOnly(S) == { x \in S : Cardinality({ y \in S : y <= x }) = Cardinality({ y \in S : y < x }) }

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

ExploreFrontier ==
  /\ frontier # {}
  /\ CHOOSE n \in frontier :
       \/ (n \notin marked /\ marked' = marked \cup {n} /\ frontier' = frontier \cup Succ[n])
       \/ (n \in marked /\ frontier' = frontier \ {n} /\ marked' = marked)
  /\ pc' = "running"

Terminate ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == ExploreFrontier \/ Terminate

Spec == Init /\ [][Next]_vars

WeakFairness == WF_vars(ExploreFrontier)

Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 == (marked \cup frontier) \subseteq Nodes /\ (marked \cup frontier) = Nodes

Inv3 == {n \in Nodes : \E m \in frontier : n \in Succ[m]}

PartialCorrectness == (marked \cup frontier) = Nodes

Termination == (marked \cup frontier) = Nodes ~> (frontier = {})

====