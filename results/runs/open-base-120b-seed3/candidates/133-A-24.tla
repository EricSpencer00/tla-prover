---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* ----------------------------------------------------------------------
   A finite (bounded) version of the generic Seq operator from the
   Sequences module.  Sequences are limited to length at most the number
   of nodes, ensuring a finite state space for model checking.
   ---------------------------------------------------------------------- *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* ----------------------------------------------------------------------
   Graph successor operator used in the configuration.  After the
   .cfg substitution, every occurrence of Succ in the parallel algorithm
   is replaced by this operator.  It simply looks up the successor set
   from the constant function Succ.
   ---------------------------------------------------------------------- *)
ConnectedToSomeButNotAll(n) == Succ[n]

(* ----------------------------------------------------------------------
   Specification, invariant and refinement property are inherited
   unchanged from the parallel reachability algorithm.
   ---------------------------------------------------------------------- *)
Spec == ParReach!Spec

Inv == ParReach!Inv

Refines == ParReach!Refines

====