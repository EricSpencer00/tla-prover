---- MODULE MCParReach ----
EXTENDS Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(*-----------------------------------------------------------------
  Graph definition: 4 nodes, each node has exactly two successors.
  The configuration substitutes the original Succ operator with
  ConnectedToSomeButNotAll defined below.
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      CASE n = 0 -> {1, 2}
      [] n = 1 -> {2, 3}
      [] n = 2 -> {3, 0}
      [] n = 3 -> {0, 1}
  ]

(*-----------------------------------------------------------------
  Bounded sequence operator used in place of the unbounded Seq.
-----------------------------------------------------------------*)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*-----------------------------------------------------------------
  Specification, invariant and property aliases that expose the
  definitions from the parallel reachability algorithm.
-----------------------------------------------------------------*)
Spec == ParReach!Spec

Inv == ParReach!Inv

Refines == ParReach!Refines

====