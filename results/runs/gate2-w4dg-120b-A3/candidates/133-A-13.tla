---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs
vars == <<marked, frontier, pc, sel, succs>>

SuccAll(x) == Succ[x]
Seq == [0 .. Cardinality(Nodes) -> Nodes \cup {"none"}]

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "active", "done"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = SuccAll(Root)
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

Activate(p) ==
  /\ pc[p] = "idle"
  /\ frontier # {}
  /\ \E y \in frontier:
       /\ sel' = [sel EXCEPT ![p] = y]
       /\ frontier' = frontier \ {y}
       /\ pc' = [pc EXCEPT ![p] = "active"]
  /\ succs' = [succs EXCEPT ![p] = SuccAll(sel[p])]

Mark(p) ==
  /\ pc[p] = "active"
  /\ succs[p] # {}
  /\ \E y \in succs[p]:
       /\ succs' = [succs EXCEPT ![p] = succs[p] \ {y}]
       /\ marked' = marked \cup {y}
       /\ frontier' = frontier \cup SuccAll(y)
  /\ UNCHANGED <<pc, sel>>

Deactivate(p) ==
  /\ pc[p] = "active"
  /\ succs[p] = {}
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<marked, frontier, sel, succs>>

Next ==
  \/ \E p \in Procs: Activate(p)
  \/ \E p \in Procs: Mark(p)
  \/ \E p \in Procs: Deactivate(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TRUE

\* Operators substituted by the .cfg: ConnectedToSomeButNotAll overrides Succ
\* and LimitedSeq overrides Seq, so they are defined here and never used elsewhere.
ConnectedToSomeButNotAll(x) == SuccAll(x)
LimitedSeq == Seq
====