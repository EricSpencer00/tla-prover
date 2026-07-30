---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

\* Model-checking configuration module for the sequential Misra reachability
\* algorithm. This module binds the otherwise abstract graph and sequence
\* types to concrete, finite values so that TLC can exhaustively explore the
\* reachable state space. It does NOT modify the underlying algorithm -- it
\* only supplies values for its parameters.

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "running"

Explore(v) ==
  /\ frontier = {v}
  /\ frontier' = Succ[v]
  /\ marked' = marked \cup Succ[v]
  /\ pc' = IF frontier = {} THEN "done" ELSE "running"

Done == (pc = "done") /\ UNCHANGED vars

Next ==
  \/ \E v \in Nodes : Explore(v)
  \/ Done

Spec == Init /\ [][Next]_vars

\* Invariant: all frontier nodes are already part of the marked set.
Inv1 == frontier \subseteq marked

\* Invariant: every node reachable from the marked set via a successor step
\* is already in the marked set (no newly reachable nodes left out).
Inv2 ==
  \A x \in Nodes :
    ( \E y \in marked : x \in Succ[y] ) => x \in marked

\* Invariant: the frontier is exactly the set of unmarked successors of the
\* already-marked set -- nothing else is on the frontier, nothing is missing.
Inv3 == frontier = { x \in Nodes : \E y \in marked : x \in Succ[y] /\ x \notin marked }

\* Invariant: every node marked by the algorithm is reachable from the Root
\* via a concrete path of length at most the number of nodes (the sequence
\* bound that makes the otherwise infinite path set finite for TLC).
PartialCorrectness ==
  \A v \in marked :
    \E s \in Seq :
      /\ Len(s) <= Cardinality(Nodes)
      /\ s[1] = Root
      /\ s[Len(s)] = v
      /\ \A k \in 1 .. (Len(s) - 1) : s[k + 1] \in Succ[s[k]]

\* Liveness: the algorithm eventually reaches a completed state, even on the
\* longest-running path through the graph.
Termination == <>(pc = "done")

====