---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets, MCSeq, MCParallelReach

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succ

vars == <<marked, frontier, pc, sel, succ>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> 0..2]
  /\ sel \in [Procs -> Seq(Nodes)]
  /\ succ \in [Nodes -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = [p \in Procs |-> 0]
  /\ sel = [p \in Procs |-> <<>>]
  /\ succ = Succ

Work(p) ==
  /\ pc[p] = 0
  /\ frontier # {}
  /\ Cardinality(frontier) <= Cardinality(Nodes)
  /\ \E v \in frontier :
       /\ sel' = [sel EXCEPT ![p] = Append(@, v)]
       /\ frontier' = frontier \ {v}
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED <<marked, succ>>

Mark(p) ==
  /\ pc[p] = 1
  /\ sel[p] # <<>>
  /\ Head(sel[p]) \notin marked
  /\ marked' = marked \cup {Head(sel[p])}
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED <<frontier, sel, succ>>

Expand(p) ==
  /\ pc[p] = 1
  /\ sel[p] # <<>>
  /\ Head(sel[p]) \in marked
  /\ frontier' = frontier \cup succ[Head(sel[p])]
  /\ sel' = [sel EXCEPT ![p] = Tail(@)]
  /\ pc' = [pc EXCEPT ![p] = 0]
  /\ UNCHANGED <<marked, succ>>

Finish(p) ==
  /\ pc[p] = 2
  /\ sel[p] = <<>>
  /\ pc' = [pc EXCEPT ![p] = 0]
  /\ UNCHANGED <<marked, frontier, sel, succ>>

Next ==
  \/ \E p \in Procs : Work(p) \/ Mark(p) \/ Expand(p) \/ Finish(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == ImplementsMisra

ConnectedToSomeButAll == Cardinality(Nodes) = 4 /\ Succ = [v \in Nodes |-> {w \in Nodes : w # v}]

LimitedSeq == Seq

====