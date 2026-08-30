---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, selected, succs

vars == <<marked, frontier, pc, selected, succs>>

MaxLen == Cardinality(Nodes)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working"}]
  /\ selected \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> Seq(Nodes)]

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> << >>]

StartWork(p) ==
  /\ pc[p] = "idle"
  /\ \E n \in frontier :
       /\ frontier' = frontier \ {n}
       /\ marked' = marked \cup {n}
       /\ selected' = [selected EXCEPT ![p] = n]
       /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ pc' = [pc EXCEPT ![p] = "working"]

Advance(p) ==
  /\ pc[p] = "working"
  /\ Len(succs[p]) < MaxLen
  /\ succs' = [succs EXCEPT ![p] = Append(succs[p], SelectedSuccessor(p))]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ selected' = [selected EXCEPT ![p] = "none"]
  /\ frontier' = frontier \cup ConnectedToSomeButNotAll(SelectedSuccessor(p))
  /\ UNCHANGED marked

SelectedSuccessor(p) ==
  IF Succ[selected[p]] = {}
  THEN selected[p]
  ELSE CHOOSE x \in Succ[selected[p]] : TRUE

Next == \E p \in Procs : StartWork(p) \/ Advance(p)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ \A p \in Procs : pc[p] \in {"idle", "working"}
  /\ \A p \in Procs : pc[p] = "working" => selected[p] \in Nodes
  /\ \A p \in Procs : pc[p] = "working" => Len(succs[p]) <= MaxLen

Refines ==
  /\ \A p \in Procs : selected[p] \in Nodes => selected[p] \in marked
  /\ \A p \in Procs : Len(succs[p]) > 0 => succs[p][1] \in marked

ConnectedToSomeButNotAll(n) ==
  { m \in Succ[n] : (n \in marked) /\ (m \notin marked) }

LimitedSeq == Seq

====