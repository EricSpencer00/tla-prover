---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(*-----------------------------------------------------------------
  Concrete graph definition: each node has exactly two successors.
  This operator will be substituted for the constant Succ by the
  .cfg file.
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      { (n % Cardinality(Nodes)) + 1,
        ((n + 1) % Cardinality(Nodes)) + 1 } ]

(*-----------------------------------------------------------------
  A finite version of Seq limited to sequences of length at most |Nodes|.
  The .cfg file substitutes Seq with this operator.
-----------------------------------------------------------------*)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*-----------------------------------------------------------------
  Specification, initialization, next-state relation, invariant and
  refinement property are taken directly from the parallel algorithm
  specification (module ParReach).
-----------------------------------------------------------------*)
Spec == ParReach!Spec
Init == ParReach!Init
Next == ParReach!Next

Inv == ParReach!Inv
Refines == ParReach!Refines

====