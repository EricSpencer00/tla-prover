---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Bounded successor operator used by the .cfg substitution *)
ConnectedToSomeButNotAll(n) == 
    IF n \in Nodes THEN Succ[n] \cap Nodes ELSE {}

(* Finite version of Seq for model checking *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Specification, invariant and refinement property from the parallel algorithm *)
Spec == ParReach!Spec
Inv == ParReach!Inv
Refines == ParReach!Refines

====