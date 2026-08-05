---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, MCParReachStd

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succset

vars == <<marked, frontier, pc, sel, succset>>

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in [Procs -> {"idle", "selecting", "expanding"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succset \in [Procs -> Seq(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = Nodes
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succset = [p \in Procs |-> <<>>]

Select ==
  /\ \E p \in Procs, v \in frontier :
       /\ pc[p] = "idle"
       /\ v \notin marked
       /\ marked' = marked \cup {v}
       /\ sel' = [sel EXCEPT ![p] = v]
       /\ pc' = [pc EXCEPT ![p] = "selecting"]
  /\ UNCHANGED <<frontier, succset>>

Expand ==
  /\ \E p \in Procs :
       /\ pc[p] = "selecting"
       /\ succset' = [succset EXCEPT ![p] = <<sel[p]>> \o <<SelectNode(p)>>]
       /\ pc' = [pc EXCEPT ![p] = "expanding"]
  /\ UNCHANGED <<marked, frontier, sel>>

Next == Select \/ Expand

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TRUE

LimitedSeq == Sequences.Seq
SuccSet == Succ

====