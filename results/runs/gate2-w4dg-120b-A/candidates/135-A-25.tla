---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES
  marked,
  frontier,
  pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in 0..3

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = 0

Explore ==
  /\ pc = 0
  /\ frontier # {}
  /\ marked' = marked \cup frontier
  /\ frontier' = { y \in Nodes : \E x \in frontier : y \in Succ[x] }
  /\ pc' = 1

ExploreComplete ==
  /\ pc = 0
  /\ frontier = {}
  /\ pc' = 3
  /\ UNCHANGED <<marked, frontier>>

CheckReachable ==
  /\ pc = 1
  /\ \A n \in Nodes : n \in marked
  /\ pc' = 2
  /\ UNCHANGED <<marked, frontier>>

Done ==
  /\ pc = 2
  /\ pc' = 3
  /\ UNCHANGED <<marked, frontier>>

InitPhase == Init \/ Explore \/ ExploreComplete \/ CheckReachable \/ Done

Next == InitPhase

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore) /\ WF_vars(CheckReachable)

Inv1 ==
  /\ frontier \subseteq Nodes
  /\ frontier \subseteq { y \in Nodes : \E x \in marked : y \in Succ[x] }

Inv2 ==
  /\ marked \subseteq { n \in Nodes : \E m \in Nodes, k \in 1..Cardinality(Nodes) : Seq(k) = n /\ Seq(1) = Root /\ \A i \in 1..(k - 1) : Seq(i + 1) \in Succ[Seq(i)] }

Inv3 ==
  /\ marked \cup frontier = { n \in Nodes : \E m \in Nodes, k \in 1..Cardinality(Nodes) : Seq(k) = n /\ Seq(1) = Root /\ \A i \in 1..(k - 1) : Seq(i + 1) \in Succ[Seq(i)] }

PartialCorrectness ==
  \A n \in Nodes : n \in marked => n \in { y \in Nodes : \E x \in marked : y \in Succ[x] }

Termination == <>(pc = 3)

====