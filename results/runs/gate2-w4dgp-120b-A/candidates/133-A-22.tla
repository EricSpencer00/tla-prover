---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, selected, succs

vars == <<marked, frontier, pc, selected, succs>>

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in [Procs -> 0..3]
  /\ selected \in [Procs -> Nodes]
  /\ succs \in [Procs -> Seq(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = [p \in Procs |-> 0]
  /\ selected = [p \in Procs |-> Root]
  /\ succs = [p \in Procs |-> << >>]

Choose(p) ==
  /\ pc[p] = 0
  /\ \E v \in frontier :
       /\ selected' = [selected EXCEPT ![p] = v]
       /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED <<marked, frontier>>

Traverse(p) ==
  /\ pc[p] = 1
  /\ \E n \in Nodes :
       /\ succs' = [succs EXCEPT ![p] = Append(succs[p], n)]
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED <<marked, frontier, selected>>

Commit(p) ==
  /\ pc[p] = 2
  /\ selected[p] \notin marked
  /\ marked' = marked \cup {selected[p]}
  /\ frontier' = frontier \cup succs[p]
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ selected' = [selected EXCEPT ![p] = Root]
  /\ pc' = [pc EXCEPT ![p] = 0]

Next ==
  \/ \E p \in Procs : Choose(p)
  \/ \E p \in Procs : Traverse(p)
  \/ \E p \in Procs : Commit(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == Refinement

FOUR == 4
ConnectedToSomeButNotAll == Succ
LimitedSeq == Seq

====