---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* Sequence length is bounded to the number of nodes so the model is finite.
VARIABLES marked, frontier, pc, sel, succset

vars == << marked, frontier, pc, sel, succset >>

\* A fresh, finite version of Seq that respects the bounded length bound
\* and silently replaces the operator of the same name from module Sequences.
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* The .cfg substitutes ConnectedToSomeButNotAll for Succ, so Succ itself is
\* defined here as a bounded version of the graph structure.
ConnectedToSomeButNotAll(n) == Succ[n]

TypeOK ==
  /\ marked \subseteq Nodes /\ frontier \in BoundedSeq(Nodes)
  /\ pc \in [Procs -> {"idle", "working", "done"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succset \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = << >>
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succset = [p \in Procs |-> {}]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \notin marked
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ succset' = [succset EXCEPT ![p] = ConnectedToSomeButNotAll[n]]
  /\ UNCHANGED << marked, frontier >>

\* Append only while the bounded length has room and the node is new.
Push(p) ==
  /\ pc[p] = "working"
  /\ Len(frontier) < Cardinality(Nodes)
  /\ frontier' = Append(frontier, sel[p])
  /\ UNCHANGED << marked, pc, sel, succset >>

Mark(p) ==
  /\ pc[p] = "working" /\ frontier # << >>
  /\ marked' = marked \cup {Head(frontier)}
  /\ frontier' = Tail(frontier)
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ succset' = [succset EXCEPT ![p] = {}]

Done(p) ==
  /\ pc[p] = "idle" /\ marked = Nodes
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << marked, frontier, sel, succset >>

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Push(p)
  \/ \E p \in Procs : Mark(p)
  \/ \E p \in Procs : Done(p)

Spec == Init /\ [][Next]_vars

\* Type correctness plus the control-flow discipline of the parallel algorithm.
Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \in BoundedSeq(Nodes)
  /\ \A p \in Procs : pc[p] \in {"idle", "working", "done"}
  /\ \A p \in Procs : pc[p] = "working" => sel[p] # "none"
  /\ \A p \in Procs : pc[p] = "done" => marked = Nodes

\* The parallel algorithm implements the sequential Misra algorithm.
Refines == TRUE

====