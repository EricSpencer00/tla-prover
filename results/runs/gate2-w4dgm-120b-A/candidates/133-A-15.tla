---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc, selected, succs

vars == <<marked, frontier, pc, selected, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working", "done"}]
  /\ selected \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> Seq(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> << >>]

Acquire(p) ==
  /\ pc[p] = "idle"
  /\ frontier # {}
  /\ \E v \in frontier :
       /\ frontier' = frontier \ {v}
       /\ selected' = [selected EXCEPT ![p] = v]
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ UNCHANGED marked

Extend(p) ==
  /\ pc[p] = "working"
  /\ succs[p] # << >>
  /\ Len(succs[p]) < Cardinality(Nodes)
  /\ \E w \in Succ[selected[p]] :
       succs' = [succs EXCEPT ![p] = Append(succs[p], w)]
  /\ UNCHANGED <<marked, frontier, pc, selected>>

Settle(p) ==
  /\ pc[p] = "working"
  /\ succs[p] # << >>
  /\ LET w == succs[p][Len(succs[p])] IN
       \/ (    w \notin marked
           /\ marked' = marked \cup {w}
           /\ frontier' = frontier \cup {w}
       )
       /\ succs' = [succs EXCEPT ![p] = Tail(succs[p])]
  /\ UNCHANGED <<pc, selected>>

Finish(p) ==
  /\ pc[p] = "working"
  /\ succs[p] = << >>
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<marked, frontier, selected, succs>>

IdleStep == UNCHANGED vars

Next ==
  \/ \E p \in Procs : Acquire(p)
  \/ \E p \in Procs : Extend(p)
  \/ \E p \in Procs : Settle(p)
  \/ \E p \in Procs : Finish(p)
  \/ IdleStep

Spec == Init /\ [][Next]_vars

Inv ==
  /\ marked \cup frontier = Nodes
  /\ marked \cap frontier = {}
  /\ \A p \in Procs : selected[p] \in Nodes => selected[p] \in marked
  /\ \A p \in Procs : succs[p] # << >> => Len(succs[p]) <= Cardinality(Nodes)
  /\ \A p \in Procs : succs[p] # << >> => succs[p][1] \in Succ[selected[p]]

Refines ==
  /\ \A v \in Nodes : (v \in frontier) ~> (v \in marked)
  /\ \A p \in Procs : (pc[p] = "working") ~> (pc[p] = "done")

ConnectedToSomeButNotAll(v) == Succ[v]

LimitedSeq == Seq

====