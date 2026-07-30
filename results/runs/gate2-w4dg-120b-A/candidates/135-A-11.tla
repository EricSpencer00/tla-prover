---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"exploring", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "exploring"

Explore(n) ==
  /\ pc = "exploring"
  /\ n \in frontier
  /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
  /\ marked' = marked \cup Succ[n]
  /\ pc' = IF frontier = {n} THEN "done" ELSE pc

Next == \E n \in Nodes : Explore(n)

Spec == Init /\ [][Next]_vars

Inv1 == frontier \subseteq marked

Inv2 == marked \subseteq (UNION {Succ[n] : n \in marked})

Inv3 == marked \subseteq {x \in Nodes : \E s \in Seq : s[1] = Root /\ s[Len(s)] = x}

PartialCorrectness == marked = {x \in Nodes : \E s \in Seq : s[1] = Root /\ s[Len(s)] = x}

Termination == <>(pc = "done")

====