---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, MCParReachBase

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs
vars == <<marked, frontier, pc, sel, succs>>

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> 0]
  /\ succs = [p \in Procs |-> << >>]

Next ==
  \/ \E p \in Procs :
       /\ pc[p] = "idle"
       /\ frontier # {}
       /\ \E v \in frontier :
            /\ marked' = marked \cup {v}
            /\ frontier' = frontier \cup Succ[v]
            /\ sel' = [sel EXCEPT ![p] = v]
            /\ succs' = [succs EXCEPT ![p] = Succ[v]]
       /\ pc' = [pc EXCEPT ![p] = "done"]
  \/ \E p \in Procs :
       /\ pc[p] = "done"
       /\ frontier = {}
       /\ frontier' = frontier \cup succs[p]
       /\ pc' = [pc EXCEPT ![p] = "idle"]
  \/ \E p \in Procs :
       /\ pc[p] = "idle"
       /\ frontier = {}
       /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A p \in Procs : sel[p] \in Nodes
  /\ \A p \in Procs : Len(succs[p]) = (IF frontier = {} THEN 0 ELSE 1)

Refines ==
  \A p \in Procs : sel[p] \in marked

ConnectedToSomeButNotAll == Succ

LimitedSeq == Seq

====