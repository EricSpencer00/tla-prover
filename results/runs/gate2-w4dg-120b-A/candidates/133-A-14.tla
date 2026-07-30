---- MODULE MCParReach ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

RECURSIVE Range(_)
Range(s) ==
  IF s = << >> THEN {}
  ELSE {Head(s)} \cup Range(Tail(s))

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "active"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> Seq]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> << >>]

Activate(p) ==
  /\ pc[p] = "idle"
  /\ \E n \in frontier :
       /\ sel' = [sel EXCEPT ![p] = n]
       /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "active"]
  /\ UNCHANGED <<marked, succs>>

Push(p) ==
  /\ pc[p] = "active"
  /\ Len(succs[p]) < Seq
  /\ \E n \in Succ[sel[p]] :
       succs' = [succs EXCEPT ![p] = Append(@, n)]
  /\ UNCHANGED <<marked, frontier, pc, sel>>

Mark(p) ==
  /\ succs[p] # << >>
  /\ marked' = marked \cup {Head(succs[p])}
  /\ frontier' = frontier \cup {Head(succs[p])}
  /\ succs' = [succs EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<pc, sel>>

Done(p) ==
  /\ pc[p] = "active"
  /\ succs[p] = << >>
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ UNCHANGED <<marked, frontier, succs>>

Next ==
  \/ \E p \in Procs : Activate(p)
  \/ \E p \in Procs : Push(p)
  \/ \E p \in Procs : Mark(p)
  \/ \E p \in Procs : Done(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TRUE

====