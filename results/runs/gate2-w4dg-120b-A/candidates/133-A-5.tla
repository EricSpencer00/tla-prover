---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, sel, succSet

vars == <<marked, frontier, pc, sel, succSet>>

Init ==
  /\ marked = {Root} \cup Succ[Root]
  /\ frontier = Succ[Root]
  /\ pc = [p \in Procs |-> 0]
  /\ sel = [p \in Procs |-> 0]
  /\ succSet = [p \in Procs |-> Seq]

Select(p, n) ==
  /\ pc[p] = 0
  /\ frontier = {}
  /\ frontier' = {n}
  /\ marked' = marked \cup {n}
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ succSet' = [succSet EXCEPT ![p] = << >>]
  /\ UNCHANGED << >>

Explore(p, x) ==
  /\ pc[p] = 1
  /\ Len(succSet[p]) < Seq
  /\ succSet' = [succSet EXCEPT ![p] = Append(succSet[p], x)]
  /\ UNCHANGED << marked, frontier, pc, sel >>

Complete(p) ==
  /\ pc[p] = 1
  /\ Len(succSet[p]) = Seq
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED << marked, frontier, sel, succSet >>

Finalize(p) ==
  /\ pc[p] = 2
  /\ pc' = [pc EXCEPT ![p] = 3]
  /\ UNCHANGED << marked, frontier, sel, succSet >>

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs, x \in Nodes : Explore(p, x)
  \/ \E p \in Procs : Complete(p)
  \/ \E p \in Procs : Finalize(p)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A p \in Procs : pc[p] \in 0..3
  /\ \A p \in Procs : succSet[p] \in SeqOf(Nodes, Seq)
  /\ \A n \in frontier : n \notin marked

Refines == Inv

====