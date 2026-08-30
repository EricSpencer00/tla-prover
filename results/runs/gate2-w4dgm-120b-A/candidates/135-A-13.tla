---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "ongoing"

Explore(n) ==
  /\ pc = "ongoing"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ marked' = marked \cup Succ[n]
  /\ frontier' = frontier' \cup Succ[n]
  /\ pc' = IF frontier' = {} THEN "done" ELSE pc

Next ==
  \E n \in Nodes : Explore(n)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"ongoing", "done"}

Inv1 ==
  (\A n \in Nodes : n \in frontier => n \in marked) /\ \A n \in Nodes : n \in marked => n \in frontier \/ n = Root

Inv2 ==
  \A n \in Nodes : n \in marked => (\E m \in Nodes : n \in Succ[m])

Inv3 ==
  \A n \in Nodes : n \in marked <=> (\E p \in LimitedSeq(Nodes) : p # [] /\ p[1] = Root /\ \A i \in 1..(Len(p) - 1) : p[i + 1] \in Succ[p[i]] /\ p[Len(p)] = n)

PartialCorrectness ==
  \A n \in Nodes : n \in marked => (\E p \in LimitedSeq(Nodes) : p # [] /\ p[1] = Root /\ \A i \in 1..(Len(p) - 1) : p[i + 1] \in Succ[p[i]] /\ p[Len(p)] = n)

Termination ==
  \A n \in Nodes : (n \in frontier) ~> (n \notin frontier)

ConnectedToSomeButNotAll ==
  \E x \in Nodes : \E y \in Nodes : y \in Succ[x]

LimitedSeq ==
  [n \in Nodes, m \in Nodes |-> ConnectedToSomeButNotAll]
====