---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

SuccOf == [x \in Nodes |-> Succ[x]]

VARIABLES marked, frontier, pc, target, succs

vars == <<marked, frontier, pc, target, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "selecting", "reading", "pushing"}]
  /\ target \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ target = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

Select(p) ==
  /\ pc[p] = "idle"
  /\ \E n \in frontier :
       /\ frontier' = frontier \ {n}
       /\ target' = [target EXCEPT ![p] = n]
       /\ succs' = [succs EXCEPT ![p] = SuccOf[n]]
  /\ pc' = [pc EXCEPT ![p] = "selecting"]
  /\ UNCHANGED marked

ReadFresh(p) ==
  /\ pc[p] = "selecting"
  /\ succs[p] \subseteq marked
  /\ pc' = [pc EXCEPT ![p] = "reading"]
  /\ UNCHANGED <<marked, frontier, target, succs>>

Push(p) ==
  /\ pc[p] = "selecting"
  /\ succs[p] \not\subseteq marked
  /\ frontier' = frontier \cup succs[p]
  /\ marked' = marked \cup succs[p]
  /\ pc' = [pc EXCEPT ![p] = "pushing"]
  /\ UNCHANGED <<target, succs>>

Reset(p) ==
  /\ pc[p] \in {"reading", "pushing"}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ target' = [target EXCEPT ![p] = "none"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E p \in Procs : Select(p)
  \/ \E p \in Procs : ReadFresh(p)
  \/ \E p \in Procs : Push(p)
  \/ \E p \in Procs : Reset(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TypeOK

ConnectedToSomeButNotAll == Succ
LimitedSeq == Seq

====