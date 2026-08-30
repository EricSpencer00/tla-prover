---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "active"

Advance(p, q) ==
  /\ pc = "active"
  /\ p \in frontier
  /\ q \in Succ[p]
  /\ q \notin marked
  /\ marked' = marked \cup {q}
  /\ frontier' = (frontier \ {p}) \cup {q}
  /\ pc' = pc

IdleStep ==
  /\ pc = "active"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E p \in Nodes, q \in Nodes : Advance(p, q)
  \/ IdleStep

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"active", "done"}

Inv1 == \A q \in marked : \E p \in marked : q \in Succ[p]
Inv2 == marked = {q \in Nodes : \E seq \in LimitedSeq(Root, q) : TRUE}
Inv3 == frontier = {q \in Nodes : \A p \in Nodes \ marked : q \notin Succ[p]}
PartialCorrectness == \A q \in Nodes : (\E p \in Nodes : q \in Succ[p]) => q \in marked

Termination == <>(pc = "done")

ConnectedToSomeButNotAll == Succ

LimitedSeq(a, b) == {s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) /\ s[1] = a /\ s[Len(s)] = b}
====