---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach, Seq

CONSTANTS Nodes, Root, Procs, Succ

SuccRel == Succ

VARIABLES marked, frontier, pc, sel, succ

vars == <<marked, frontier, pc, sel, succ>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succ \in [Procs -> Seq(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succ = [p \in Procs |-> <<>>]

\* An idle process takes a frontier node and picks a successor of it.
Choose(p, y) ==
  /\ pc[p] = "idle"
  /\ frontier # {}
  /\ \E x \in frontier :
       frontier' = frontier \ {x}
       /\ sel' = [sel EXCEPT ![p] = x]
  /\ \E z \in SuccRel[sel[p]] :
       succ' = [succ EXCEPT ![p] = <<z>>]
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ UNCHANGED marked

\* A working process moves a frontier node into the shared marked set.
Mark(p) ==
  /\ pc[p] = "working"
  /\ marked' = marked \cup {sel[p]}
  /\ frontier' = frontier \cup succ[p]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ succ' = [succ EXCEPT ![p] = <<>>]

Next ==
  \/ \E p \in Procs, y \in Nodes : Choose(p, y)
  \/ \E p \in Procs : Mark(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == WF_vars(Mark(1))

====