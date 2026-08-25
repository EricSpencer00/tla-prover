---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, ParallelReach

CONSTANTS Nodes, Root, Procs, Succ

(*-------------------------------------------------------------------------
   Concrete graph used for model checking.
   Each node has exactly two distinct successors chosen from the other nodes.
   This operator replaces the abstract Succ operator via the .cfg file.
--------------------------------------------------------------------------*)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      CHOOSE S \in SUBSET (Nodes \ {n}) : Cardinality(S) = 2 ]

(*-------------------------------------------------------------------------
   A finite version of the sequence operator.
   It limits sequences of Nodes to length at most |Nodes|.
   This operator replaces Seq from the Sequences module via the .cfg file.
--------------------------------------------------------------------------*)
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

(*-------------------------------------------------------------------------
   Specification, invariant, and refinement property are inherited from the
   parallel reachability algorithm specification.
--------------------------------------------------------------------------*)
Spec    == ParallelReach!Spec
Inv     == ParallelReach!Inv
Refines == ParallelReach!Refines

====