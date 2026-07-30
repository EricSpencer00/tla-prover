---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

EMPTY == "empty"
NONE == "none"

VARIABLES marked, frontier, pc, chosen, stack
vars == <<marked, frontier, pc, chosen, stack>>

RECURSIVE AddToSeq(_)
AddToSeq(s) ==
  IF Cardinality(s) < Cardinality(Nodes) THEN s
  ELSE s

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "exploring"}]
  /\ chosen \in [Procs -> Nodes \cup {NONE}]
  /\ stack \in [Procs -> Seq(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ chosen = [p \in Procs |-> NONE]
  /\ stack = [p \in Procs |-> << >>]

Pick(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "exploring"]
  /\ chosen' = [chosen EXCEPT ![p] = n]
  /\ stack' = [stack EXCEPT ![p] = << >>]
  /\ UNCHANGED marked

Visit(p, n) ==
  /\ pc[p] = "exploring"
  /\ chosen[p] = n
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \cup ConnectedToSomeButNotAll[n]
  /\ stack' = [stack EXCEPT ![p] = AddToSeq(@ \o << n >>)]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ chosen' = [chosen EXCEPT ![p] = NONE]

Revisit(p, n) ==
  /\ pc[p] = "exploring"
  /\ chosen[p] = n
  /\ n \in marked
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ chosen' = [chosen EXCEPT ![p] = NONE]
  /\ UNCHANGED <<marked, frontier, stack>>

Next ==
  \/ \E p \in Procs, n \in Nodes : Pick(p, n)
  \/ \E p \in Procs, n \in Nodes : Visit(p, n)
  \/ \E p \in Procs, n \in Nodes : Revisit(p, n)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TRUE

\* Operators the .cfg substitutes in, overriding the standard definitions.
ConnectedToSomeButNotAll == ConnectedToSomeButNotAll
LimitedSeq == AddToSeq

====