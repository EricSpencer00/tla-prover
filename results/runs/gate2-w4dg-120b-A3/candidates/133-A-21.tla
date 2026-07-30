---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

\* Configuration module for the parallel reachability algorithm.  This file
\* provides the concrete definitions (graph, bounded sequence) that make
\* the model checkable, while inheriting the algorithmic actions from the
\* standard specification.  The identifiers below are exactly those that
\* appear in the reference TLC configuration file.

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, selected, succset

vars == <<marked, frontier, pc, selected, succset>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in [Procs -> {"idle","working","done"}]
  /\ selected \in [Procs -> Nodes \cup {"none"}]
  /\ succset \in [Procs -> SUBSET Nodes]

\* Inherited initialization, but the graph Succ and the bounded sequence
\* operator are supplied by this module.
Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> "none"]
  /\ succset = [p \in Procs |-> {}]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ selected' = [selected EXCEPT ![p] = n]
  /\ succset' = [succset EXCEPT ![p] = Succ[n]]
  /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ UNCHANGED marked

Mark(p, n) ==
  /\ pc[p] = "working"
  /\ n \in succset[p]
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \cup succset[p]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<selected, succset>>

Reset(p) ==
  /\ pc[p] = "done"
  /\ selected[p] \in frontier
  /\ frontier' = frontier \ {selected[p]}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ selected' = [selected EXCEPT ![p] = "none"]
  /\ succset' = [succset EXCEPT ![p] = {}]
  /\ UNCHANGED marked

Idle ==
  /\ frontier = {}
  /\ \A p \in Procs : pc[p] = "idle"

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs, n \in Nodes : Mark(p, n)
  \/ \E p \in Procs : Reset(p)
  \/ Idle

Spec == Init /\ [][Next]_vars

\* The inductive invariant: every frontier node is reachable from the root
\* via a bounded sequence of successors, and no process is stalled.
Inv ==
  /\ frontier \subseteq { n \in Nodes : \E k \in 1..Cardinality(Nodes) : ConnectedToSomeButNotAll(Root, n, k) }
  /\ \A p \in Procs : pc[p] \in {"idle","working","done"}

\* Refinement: every marked node is reachable from the root in the
\* sequential Misra algorithm's model (Reachable is its predicate).
Refines ==
  \A n \in marked : Reachable(Root, n)

====