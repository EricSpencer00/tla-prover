---- MODULE MCParReach ----
CONSTANTS Nodes, Root, Procs, Succ

EXTENDS Sequences, ParReach

(* Concrete graph: each node has exactly two successors *)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |
      IF n = 1 THEN {2,3}
      ELSE IF n = 2 THEN {3,4}
      ELSE IF n = 3 THEN {4,1}
      ELSE {1,2} ]

(* Bounded sequences over Nodes *)
LimitedSeq ==
  { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

(* Specification, invariant and refinement property inherited from the parallel algorithm *)
Spec == ParReach!Spec
Inv == ParReach!Inv
Refines == ParReach!Refines

====