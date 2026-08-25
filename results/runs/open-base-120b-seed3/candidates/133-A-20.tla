---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Procs, Succ

(* ---------------------------------------------------------------------- *)
(* Concrete graph: 4 nodes, each with exactly two successors               *)
(* The .cfg substitutes Succ with ConnectedToSomeButNotAll, so we define   *)
(* that operator here.                                                    *)
(* ---------------------------------------------------------------------- *)
ConnectedToSomeButNotAll(n) ==
  CASE n = 1 -> {2, 3}
  [] n = 2 -> {3, 4}
  [] n = 3 -> {4, 1}
  [] n = 4 -> {1, 2}
  [] OTHER -> {}

(* ---------------------------------------------------------------------- *)
(* LimitedSeq replaces the unbounded Seq from the Sequences module.       *)
(* It restricts sequence length to at most the number of nodes.           *)
(* ---------------------------------------------------------------------- *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* ---------------------------------------------------------------------- *)
(* Instantiate the parallel reachability algorithm specification.        *)
(* The constants are supplied; the actual definitions of Succ will be    *)
(* provided by the .cfg substitution (Succ := ConnectedToSomeButNotAll).  *)
(* ---------------------------------------------------------------------- *)
INSTANCE ParReach WITH
  Nodes = Nodes,
  Root  = Root,
  Procs = Procs,
  Succ  = Succ

(* ---------------------------------------------------------------------- *)
(* Export the required identifiers.                                       *)
(* ---------------------------------------------------------------------- *)
Spec      == ParReach!Spec
Init      == ParReach!Init
Next      == ParReach!Next
Inv       == ParReach!Inv
Refines   == ParReach!Refines

====