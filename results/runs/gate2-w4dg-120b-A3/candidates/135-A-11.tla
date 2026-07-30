---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* The reachability algorithm works over a graph whose connectivity is given by
\* the custom operator ConnectedToSomeButNotAll below, which is substituted in
\* for the Succ name in the standard specification. The Sequence operator is
\* likewise overridden by a bounded version called LimitedSeq, because an
\* unbounded sequence makes the state space infinite.

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in {"idle", "running", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"

Step ==
  /\ pc = "idle"
  /\ pc' = "running"
  /\ UNCHANGED <<marked, frontier>>

Mark(v) ==
  /\ pc = "running"
  /\ v \in frontier
  /\ frontier' = (frontier \cup Succ[v]) \ marked
  /\ marked' = marked \cup Succ[v]
  /\ UNCHANGED pc

Done ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Step
  \/ \E v \in Nodes : Mark(v)
  \/ Done

Spec == Init /\ [][Next]_vars

\* The algorithm's three core invariants, plus the type invariant and the
\* partial correctness statement that every node reachable from the root is
\* actually marked once the algorithm finishes.
Inv1 ==
  \A u \in Nodes : \A v \in Nodes : (v \in Succ[u]) => (u \in marked => v \in marked)

Inv2 == \A u \in Nodes : (u \in marked) => (\E w \in Nodes : u \in Succ[w])

Inv3 == marked \cup frontier = {n \in Nodes : \E p \in Nodes : n \in Succ[p]}

PartialCorrectness == (pc = "done") => (marked = {n \in Nodes : \E p \in Nodes : n \in Succ[p]})

Termination == <>(pc = "done")

\* Each node has exactly two successors, chosen deterministically so the graph
\* is non-trivial but the model is still finite.
ConnectedToSomeButNotAll(n) ==
  CASE n = 1 -> {2, 3}
  []   n = 2 -> {3, 4}
  []   n = 3 -> {4, 1}
  []   n = 4 -> {1, 2}

\* A bounded version of Sequence: only sequences of length up to |Nodes| are
\* admitted, which is sufficient for any reachable path in this finite graph.
LimitedSeq(S) ==
  {s \in Seq(S) : Len(s) <= Cardinality(Nodes)}

Succ == ConnectedToSomeButNotAll

Seq == LimitedSeq

====