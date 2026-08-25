---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Procs, Succ

(* ---------------------------------------------------------------------- *)
(*  Operator that will be substituted for Succ in the configuration file. *)
(*  It simply returns the (finite) successor set of a node as given by   *)
(*  the constant Succ.                                                    *)
(* ---------------------------------------------------------------------- *)
ConnectedToSomeButNotAll(n) == 
  { m \in Nodes : m \in Succ[n] }

(* ---------------------------------------------------------------------- *)
(*  A finite version of the generic Seq operator.  All sequences are      *)
(*  limited to length at most the number of nodes, guaranteeing a finite  *)
(*  state space for model checking.                                       *)
(* ---------------------------------------------------------------------- *)
LimitedSeq(S) == 
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* ---------------------------------------------------------------------- *)
(*  Include the parallel reachability algorithm.  Its definition provides *)
(*  the variables, Init, Next, Inv, Refines, etc.                         *)
(* ---------------------------------------------------------------------- *)
INSTANCE ParallelReachability

(* ---------------------------------------------------------------------- *)
(*  Expose the identifiers required by the .cfg file.                     *)
(* ---------------------------------------------------------------------- *)
Spec == ParallelReachability.Spec
Inv  == ParallelReachability.Inv
Refines == ParallelReachability.Refines

====