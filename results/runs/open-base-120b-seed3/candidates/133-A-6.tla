---- MODULE MCParReach ----
EXTENDS Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

\* ----------------------------------------------------------------------
\* Concrete graph used for model checking.
\* Each of the 4 nodes has exactly two successors.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
  CASE n = 1 -> {2, 3}
  []   n = 2 -> {3, 4}
  []   n = 3 -> {4, 1}
  []   n = 4 -> {1, 2}
  []   OTHER -> {}

\* Make the constant Succ refer to the concrete graph.
Succ == ConnectedToSomeButNotAll

\* ----------------------------------------------------------------------
\* LimitedSeq replaces the unbounded Seq from the Sequences module.
\* It restricts sequence length to at most the number of nodes.
\* ----------------------------------------------------------------------
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* Specification, invariant and refinement property are taken from the
\* parallel reachability algorithm.
\* ----------------------------------------------------------------------
Spec == ParReach!Spec

Inv == ParReach!Inv

Refines == ParReach!Refines

====