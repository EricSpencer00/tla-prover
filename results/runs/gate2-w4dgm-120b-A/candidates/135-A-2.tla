---- MODULE MCReachable ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

ASSUME Succ \in [Nodes -> SUBSET Nodes]

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "running"

StepForward(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ \E m \in Succ[n] : marked' = marked \cup {m}
  /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
  /\ pc' = pc

Backtrack(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ pc' = pc
  /\ marked' = marked

Halt ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "halted"
  /\ marked' = marked
  /\ frontier' = frontier

Spec == Init /\ [][StepForward]_vars /\ [][Backtrack]_vars /\ [][Halt]_vars

TypeOK == /\ frontier \subseteq Nodes
          /\ marked \subseteq Nodes
          /\ pc \in {"running", "halted"}

Inv1 == \A a, b \in Nodes : (a \in marked /\ b \in Succ[a]) => b \in marked

Inv2 == \A n \in Nodes : (n \in frontier => n \notin marked)

Inv3 == marked = Nodes

PartialCorrectness == (pc = "halted") => (marked = Nodes)

Termination == <>(pc = "halted")

ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(S) ==
  IF S = {} THEN << >>
  ELSE LET x == CHOOSE y \in S : TRUE
           rest == LimitedSeq(S \ {x})
       IN IF Len(rest) < Cardinality(Nodes) THEN <<x>> \o rest ELSE rest
====