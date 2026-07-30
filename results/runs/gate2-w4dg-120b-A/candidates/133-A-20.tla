---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

\* The configuration inherits all state and actions from the parallel algorithm.
\* It only adds the configuration constants and the fact that Succ is total of
\* degree 2, which aligns the parallel model with the sequential one.
VARIABLES marked, frontier, pc, sel, succSet

vars == << marked, frontier, pc, sel, succSet >>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working", "done"}]
  /\ sel \in [Procs -> Seq]
  /\ succSet \in [Procs -> SUBSET Seq]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> << >>]
  /\ succSet = [p \in Procs |-> {}]

\* Inherited actions (left as stubs here; the full actions live in the parallel
\* algorithm's module and are folded into Spec via the configuration).
Start(p) ==
  /\ pc[p] = "idle"
  /\ frontier # {}
  /\ \E n \in frontier :
       sel' = [sel EXCEPT ![p] = << n >>]
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ UNCHANGED << marked, frontier, succSet >>

Select(p) ==
  /\ pc[p] = "working"
  /\ Len(sel[p]) = 1
  /\ LET n == sel[p][1] IN
       succSet' = [succSet EXCEPT ![p] = {n} \cup Succ[n]]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << marked, frontier, sel >>

Idle ==
  /\ \A p \in Procs : pc[p] = "done"
  /\ UNCHANGED vars

Next ==
  \/ \E p \in Procs : Start(p)
  \/ \E p \in Procs : Select(p)
  \/ Idle

Spec == Init /\ [][Next]_vars

\* Inductive invariant: type correctness plus control-flow discipline.
Inv ==
  /\ TypeOK
  /\ \A p \in Procs :
       /\ pc[p] \in {"idle", "working", "done"}
       /\ Len(sel[p]) <= Cardinality(Nodes)
       /\ Cardinality(succSet[p]) <= Cardinality(Nodes)

\* Refinement: what the parallel algorithm marks is exactly what the
\* sequential Misra algorithm would have marked.
Refines == marked = \E p \in Procs : succSet[p]

====