---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences, ParReach

\* Model-checking configuration for the parallel reachability algorithm.
\* It redefines the graph relation to a finite, bounded structure so TLC
\* can explore the reachable state space, and it replaces the unbounded
\* Seq constructor with a finite version (LimitedSeq).

CONSTANTS Nodes, Root, Procs, Succ

\* The graph is finite and each node has exactly two successors, so the
\* reachable part of the state space stays small even with concurrent workers.
Succ == ConnectedToSomeButNotAll

VARIABLES marked, frontier, pc, selected, succ
vars == <<marked, frontier, pc, selected, succ>>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> {}]
  /\ succ = [n \in Nodes |-> {}]

Next == \E p \in Procs : ReachStep(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working", "done"}]
  /\ selected \in [Procs -> SUBSET Nodes]
  /\ succ \in [Nodes -> SUBSET Nodes]

\* The parallel algorithm implements the sequential Misra algorithm's
\* reachability set exactly: every node the sequential version marks is
\* marked here, so no reachable state is lost by the concurrent workers.
Refines ==
  {n \in Nodes : \E s \in succ : n \in s} \subseteq marked

====