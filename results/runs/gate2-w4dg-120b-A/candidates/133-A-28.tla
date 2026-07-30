---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, sel, succset

vars == <<marked, frontier, pc, sel, succset>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> 0..1]
  /\ sel \in [Procs -> Nodes]
  /\ succset \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> 0]
  /\ sel = [p \in Procs |-> Root]
  /\ succset = [p \in Procs |-> Succ[Root]]

Select(p, n) ==
  /\ pc[p] = 0
  /\ succset' = [succset EXCEPT ![p] = {n}]
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED <<marked, frontier, sel>>

Advance(p) ==
  /\ pc[p] = 1
  /\ pc' = [pc EXCEPT ![p] = 0]
  /\ UNCHANGED <<marked, frontier, sel, succset>>

Mark(p) ==
  /\ pc[p] = 1
  /\ \E n \in succset[p] :
       /\ n \notin frontier
       /\ frontier' = frontier \cup {n}
       /\ marked' = marked \cup {n}
       /\ sel' = [sel EXCEPT ![p] = n]
       /\ succset' = [succset EXCEPT ![p] = Succ[n]]
  /\ pc' = [pc EXCEPT ![p] = 0]

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Advance(p)
  \/ \E p \in Procs : Mark(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == Inv

====