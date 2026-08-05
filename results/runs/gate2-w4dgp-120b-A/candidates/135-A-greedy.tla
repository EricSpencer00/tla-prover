---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "exploring", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"

Explore ==
  /\ pc = "idle"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ marked' = marked \cup Succ[n]
       /\ frontier' = frontier \cup Succ[n]
  /\ pc' = "exploring"

Complete ==
  /\ pc = "exploring"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Explore]_vars /\ [][Complete]_vars

Inv1 == \A n \in marked : \E m \in frontier : n \in Succ[m]
Inv2 == \A n \in frontier : \E m \in marked : n \in Succ[m]
Inv3 == marked = {n \in Nodes : \E s \in Seq(Nodes) : s # <<>> /\ Head(s) = Root /\ \A i \in 1..Len(s) : s[i] \in Nodes /\ s[Len(s)] = n}
PartialCorrectness == \A n \in Nodes : (n \in marked) <=> (n \in {n \in Nodes : \E s \in Seq(Nodes) : s # <<>> /\ Head(s) = Root /\ \A i \in 1..Len(s) : s[i] \in Nodes /\ s[Len(s)] = n})

Termination == <>(pc = "done")

ConnectedToSomeButNotAll == Succ
LimitedSeq == Seq(Nodes)
====