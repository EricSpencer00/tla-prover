---- MODULE MCParReach ----
EXTENDS Naturals

CONSTANTS Nodes, Root, Procs, Succ, Seq

MaxSeqLen == Cardinality(Nodes)

VARIABLES marked, frontier, pc, sel, succ

vars == << marked, frontier, pc, sel, succ >>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> 0..2]
  /\ sel \in [Procs -> {n \in Nodes : TRUE}]
  /\ succ \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> 0]
  /\ sel = [p \in Procs |-> Root]
  /\ succ = [p \in Procs |-> Succ[Root]]

Pick(p) ==
  /\ pc[p] = 0
  /\ \E n \in frontier :
       /\ sel' = [sel EXCEPT ![p] = n]
       /\ succ' = [succ EXCEPT ![p] = Succ[n]]
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED << marked, frontier >>

Write(p) ==
  /\ pc[p] = 1
  /\ frontier' = frontier \cup {sel[p]}
  /\ marked' = marked \cup {sel[p]}
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED << succ, sel >>

Advance(p) ==
  /\ pc[p] = 2
  /\ marked' = marked \cup succ[p]
  /\ frontier' = frontier \cup succ[p]
  /\ pc' = [pc EXCEPT ![p] = 0]
  /\ UNCHANGED << succ, sel >>

Next ==
  \/ \E p \in Procs : Pick(p)
  \/ \E p \in Procs : Write(p)
  \/ \E p \in Procs : Advance(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == Inv

====