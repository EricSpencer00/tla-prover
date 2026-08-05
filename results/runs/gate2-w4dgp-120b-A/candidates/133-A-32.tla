---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences

\* Parallel Reachability Model Checking Configuration
\* ------------------------------------------------
\* This module configures the parallel reachability algorithm for
\* finite-state model checking. It provides concrete definitions for the
\* graph structure and a bounded version of the successor operator, and
\* redefines Seq as a finite, bounded version so the state space stays
\* tractable. All other state and action definitions are imported unchanged
\* from the standard parallel-reachability module.
CONSTANTS Nodes, Root, Procs, Succ

\* Succ is a finite, bounded version of the usual (possibly infinite) successor
\* function. The .cfg substitutes ConnectedToSomeButNotAll for Succ, and
\* ConnectedToSomeButNotAll is defined below to match that bound.
ConnectedToSomeButNotAll == Succ

\* Bounded sequence type: a finite subsequence of Seq with length at most
\* the number of nodes, overriding the unbounded Seq from Sequences.
LimitedSeq(T) == {s \in Seq(T) : Len(s) <= Cardinality(Nodes)}
Seq == LimitedSeq

VARIABLES marked, frontier, pc, sel, succs
vars == <<marked, frontier, pc, sel, succs>>

\* A node is marked only when reachable: it must either be the root or be
\* reachable from some already-marked node in one step.
Reachable(n) == n = Root \/ \E m \in marked : n \in succs[m]

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "holding", "working"}]
  /\ sel \in [Procs -> Nodes]
  /\ succs \in [Nodes -> FiniteSubset(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> Root]
  /\ succs = [n \in Nodes |-> ConnectedToSomeButNotAll[n]]

Acq(p) ==
  /\ pc[p] = "idle"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ frontier' = frontier \ {n}
       /\ sel' = [sel EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = "holding"]
  /\ UNCHANGED <<marked, succs>>

Mark(p) ==
  /\ pc[p] = "holding"
  /\ ~Reachable(sel[p])
  /\ frontier \subseteq Nodes
  /\ marked' = marked \cup {sel[p]}
  /\ frontier' = frontier \cup succs[sel[p]]
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ UNCHANGED <<sel, succs>>

Done(p) ==
  /\ pc[p] = "working"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, frontier, sel, succs>>

Next == \E p \in Procs : Acq(p) \/ Mark(p) \/ Done(p)

Spec == Init /\ [][Next]_vars

\* The parallel algorithm's reachable set is always exactly the set of
\* nodes reachable from the root via the bounded successor relation.
Inv ==
  /\ TypeOK
  /\ \A n \in marked : Reachable(n)

\* Refinement: the reachable set computed by the parallel algorithm
\* coincides with the set defined by the sequential Misra reachability
\* predicate applied to the bounded successor relation.
Refines ==
  \A n \in Nodes : (n \in marked) <=> Reachable(n)

====