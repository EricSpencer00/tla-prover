---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Operator that will be substituted for Succ by the .cfg file. *)
ConnectedToSomeButNotAll == 
    { <<n, s>> : n \in Nodes /\ s \in Nodes /\ s # n }

(* A finite version of Seq, bounded by the number of nodes. *)
LimitedSeq(S) == 
    { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Specification, invariant, and refinement property are taken from the
   parallel reachability algorithm specification. *)
Spec == ParReach!Spec
Inv  == ParReach!Inv
Refines == ParReach!Refines

====