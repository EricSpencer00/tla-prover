---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete successor relation used in place of the abstract Succ constant *)
ConnectedToSomeButNotAll(n) ==
  CASE n = 1 -> {2, 3}
       [] n = 2 -> {3, 4}
       [] n = 3 -> {4, 1}
       [] n = 4 -> {1, 2}
       [] OTHER -> {}
  END CASE

(* Bounded version of Seq for model checking *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Specification, invariant and refinement property imported from the parallel algorithm *)
Spec == ParReach!Spec
Inv  == ParReach!Inv
Refines == ParReach!Refines

====