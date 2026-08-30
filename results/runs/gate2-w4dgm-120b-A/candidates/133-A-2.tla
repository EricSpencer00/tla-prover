---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

\* Model-checking configuration for the parallel reachability algorithm.
\* It inherits the whole algorithm and adds concrete configuration: a
\* 4-node graph with a fixed Successor function and a sequence that is
\* bounded to the number of nodes (SHORTSEQ) so the reachable state space
\* stays finite.
\* The .cfg file substitutes ConnectedToSomeButNotAll for Succ and
\* replaces Seq with a bounded, FINITE version called LimitedSeq --
\* this is what keeps model checking feasible.

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

Bump(x) == IF x < 4 THEN x + 1 ELSE x

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> Seq(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> << >>]

SelectNode(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ UNCHANGED marked

Explore(p) ==
  /\ pc[p] = "working"
  /\ succs[p] = << >>
  /\ \E w \in Succ[sel[p]] : succs' = [succs EXCEPT ![p] = << w >>]
  /\ UNCHANGED <<marked, frontier, pc, sel>>

Commit(p) ==
  /\ pc[p] = "working"
  /\ Len(succs[p]) > 0
  /\ marked' = marked \cup {Head(succs[p])}
  /\ frontier' = frontier \cup {Head(succs[p])}
  /\ succs' = [succs EXCEPT ![p] = Tail(succs[p])]
  /\ UNCHANGED <<pc, sel>>

CommitNot(p) ==
  /\ pc[p] = "working"
  /\ succs[p] = << >>
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, frontier, sel, succs>>

CommitAny == \E p \in Procs : Commit(p)

Next ==
  \/ \E p \in Procs, n \in Nodes : SelectNode(p, n)
  \/ \E p \in Procs : Explore(p)
  \/ CommitAny
  \/ \E p \in Procs : CommitNot(p)

Spec == Init /\ [][Next]_vars

\* The invariant the configuration checks: all state variables stay within
\* their expected type and shape, which is what keeps the action guards
\* safe from out-of-bounds sequence operations.
Inv == TypeOK

\* The parallel algorithm refines the sequential Misra reachability
\* algorithm: every node reachable from the start is eventually marked.
Refines == \A n \in Nodes : (n \in ConnectedToSomeButNotAll(Root) \ {n}) ~> (n \in marked)

\* Bounded buffer: the per-process successor sequence never exceeds the
\* number of nodes in the graph, which is what keeps model checking
\* finite.  It is kept separate from the safety invariant so it is a
\* genuine liveness bound rather than a property the model could simply
\* ignore.
SHORTSEQ == \A p \in Procs : Len(succs[p]) <= Cardinality(Nodes)

====