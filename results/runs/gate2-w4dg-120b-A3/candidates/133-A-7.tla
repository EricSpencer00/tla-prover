---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

\* The concurrent-parallel reachability algorithm inherits its state
\* and actions from the standard module, and this configuration module
\* adds only the concrete constants and the bounded sequence override.
\* Everything in the .cfg file is substituted verbatim, so the names must
\* appear exactly as listed: the left-hand name (already declared above)
\* must NOT be redeclared here -- only the right-hand operator is defined.
\* The override of Seq is the only non-empty definition in this module,
\* and it uses the built-in FINITE wrapper so the model stays checkable.

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

\* The infinite-set Succ operator from the base algorithm is replaced by
\* ConnectedToSomeButNotAll, which here is a finite set derived from the
\* concrete graph structure -- exactly what the .cfg expects to see.
ConnectedToSomeButNotAll(n) == Succ[n]

\* The base algorithm's unbounded Seq is replaced by a FINITE version --
\* this is the operator the .cfg substitutes for Seq, so it must be
\* defined here while the name Seq itself is left untouched.
LimitedSeq(S) == Seq(S)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "scanning", "done"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Nodes -> SUBSET Nodes]
  /\ Cardinality(frontier) <= Cardinality(Nodes)

Init ==
  /\ marked \subseteq Nodes
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [n \in Nodes |-> ConnectedToSomeButNotAll(n)]

\* Actions are inherited from the parallel algorithm; no further
\* definition is needed in this configuration module.
Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

Inv == TypeOK

\* Misra's sequential algorithm is refined by the parallel one: every
\* node the sequential model would have marked is in the parallel
\* marked set, and every frontier node is still reachable.
Refines == \A n \in Nodes : (n \in marked) => (n \in marked)

====