---- MODULE MCParReach ----
EXTENDS Sequences, Naturals, FiniteSets, ParReach

(*--------------------------------------------------------------------
  Constants required by the configuration.  Their concrete values are
  supplied by the .cfg file; we only declare them here to avoid
  re‑definition conflicts with the definitions already present in the
  imported modules.
--------------------------------------------------------------------*)
CONSTANTS Nodes, Root, Procs, Succ

(*--------------------------------------------------------------------
  Concrete graph: each node has exactly two successors.
  The configuration file substitutes this operator for the constant Succ.
--------------------------------------------------------------------*)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      CASE n = 1 -> {2, 3}
      [] n = 2 -> {3, 4}
      [] n = 3 -> {1, 4}
      [] n = 4 -> {1, 2} ]

(*--------------------------------------------------------------------
  A finite version of Seq: sequences over a set S whose length does not
  exceed the number of nodes.  The .cfg file substitutes this operator for
  the standard Seq operator from the Sequences module.
--------------------------------------------------------------------*)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

====