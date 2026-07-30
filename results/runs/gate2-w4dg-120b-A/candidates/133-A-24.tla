---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, sel, succset

vars == <<marked, frontier, pc, sel, succset>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "active", "done"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succset \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succset = [p \in Procs |-> {}]

Select(p, v) ==
  /\ pc[p] = "idle"
  /\ v \in frontier
  /\ pc' = [pc EXCEPT ![p] = "active"]
  /\ sel' = [sel EXCEPT ![p] = v]
  /\ succset' = [succset EXCEPT ![p] = Succ[v]]
  /\ UNCHANGED <<marked, frontier>>

Take(k, p) ==
  /\ pc[p] = "active"
  /\ k \in succset[p]
  /\ k \notin marked
  /\ marked' = marked \cup {k}
  /\ frontier' = frontier \cup {k}
  /\ UNCHANGED <<pc, sel, succset>>

Settle(p) ==
  /\ pc[p] = "active"
  /\ succset[p] = {}
  /\ sel[p] \in marked
  /\ frontier' = frontier \ {sel[p]}
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ UNCHANGED <<marked, succset>>

Next ==
  \/ \E p \in Procs, v \in Nodes : Select(p, v)
  \/ \E k \in Nodes, p \in Procs : Take(k, p)
  \/ \E p \in Procs : Settle(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == \A p \in Procs : pc[p] = "done"

====