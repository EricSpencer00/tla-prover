---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, sset

vars == <<marked, frontier, pc, sel, sset>>

Init ==
  /\ marked = {Root}
  /\ frontier = {{Root}}
  /\ pc = [p \in Procs |-> "init"]
  /\ sel = [p \in Procs |-> <<>>]
  /\ sset = [p \in Procs |-> {}]

Mark(p, n) ==
  /\ pc[p] = "working"
  /\ n \in sset[p]
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \cup {n}
  /\ sset' = [sset EXCEPT ![p] = @ \ {n}]
  /\ UNCHANGED <<pc, sel>>

Select(p) ==
  /\ pc[p] \in {"init", "working"}
  /\ frontier # {}
  /\ frontier' = frontier \ {Head(sel[p])}
  /\ sel' = [sel EXCEPT ![p] = Tail(@) \o <<Head(@)>>]
  /\ pc' = [pc EXCEPT ![p] = IF Head(sel[p]) = Root THEN "working" ELSE pc[p]]
  /\ UNCHANGED <<marked, sset>>

Explore(p) ==
  /\ pc[p] = "working"
  /\ SelCard(p) < Cardinality(Nodes)
  /\ sset' = [sset EXCEPT ![p] = @ \cup Succ[Head(sel[p])]]
  /\ UNCHANGED <<marked, frontier, pc, sel>>

Complete(p) ==
  /\ pc[p] = "working"
  /\ SelCard(p) = Cardinality(Nodes)
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<marked, frontier, sel, sset>>

SelCard(p) == Cardinality({ i \in 1..Len(sel[p]) : sel[p][i] = Head(sel[p]) })

Next ==
  \/ \E p \in Procs, n \in Nodes : Mark(p, n)
  \/ \E p \in Procs : Select(p)
  \/ \E p \in Procs : Explore(p)
  \/ \E p \in Procs : Complete(p)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A p \in Procs : pc[p] \in {"init", "working", "done"}
  /\ \A p \in Procs : sel[p] \in { x \in Seq(Nodes) : Len(x) <= Cardinality(Nodes) }
  /\ \A p \in Procs : sset[p] \subseteq Nodes

Refines == marked = Nodes

NextNoSelect ==
  \E p \in Procs, n \in Nodes : Mark(p, n)
  \/ \E p \in Procs : Explore(p)
  \/ \E p \in Procs : Complete(p)

SpecFAIR == Init /\ [][Next]_vars /\ WF_vars(NextNoSelect)

====