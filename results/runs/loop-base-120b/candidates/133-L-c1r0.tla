---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(*-----------------------------------------------------------------
  Concrete successor relation: each node has exactly two successors.
  This operator is substituted for the abstract constant Succ in the
  configuration (see ConnectedToSomeButNotAll).
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      LET a == (n % Cardinality(Nodes)) + 1 ;
          b == ((n + 1) % Cardinality(Nodes)) + 1
      IN { a , b } ]

(*-----------------------------------------------------------------
  A finite version of the sequence operator.  Sequences.Seq is
  replaced by LimitedSeq in the configuration.
-----------------------------------------------------------------*)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*-----------------------------------------------------------------
  Specification, invariant and refinement property as required by
  the .cfg file.
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

Inv == ParReach!Inv

Refines == ParReach!Refines

====