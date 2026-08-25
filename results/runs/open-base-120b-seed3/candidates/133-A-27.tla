---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, ParReach

CONSTANTS
    Nodes, \* the set of graph nodes (4 nodes in the concrete model)
    Root,   \* the distinguished start node
    Procs,  \* the set of worker processes (2 processes in the concrete model)
    Succ    \* will be replaced by ConnectedToSomeButNotAll by the .cfg file

\* ----------------------------------------------------------------------
\* Concrete graph: each node has exactly two successors.
\* The .cfg substitutes Succ with this operator, therefore we provide the
\* definition under the name ConnectedToSomeButNotAll.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      CASE n = 1 -> {2, 3}
      [] n = 2 -> {1, 4}
      [] n = 3 -> {1, 4}
      [] n = 4 -> {2, 3}
  ]

\* ----------------------------------------------------------------------
\* LimitedSeq replaces the unbounded Seq operator from the Sequences module.
\* It restricts sequence length to at most the number of nodes, guaranteeing
\* a finite state space.
\* ----------------------------------------------------------------------
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* Specification, invariant, and refinement property are taken directly from
\* the parallel reachability algorithm module (ParReach).  The names are
\* provided here so that the .cfg file can refer to them exactly.
\* ----------------------------------------------------------------------
Spec == ParSpec
Inv  == ParInv
Refines == ParRefines

====