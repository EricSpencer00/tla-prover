---- MODULE MCParReach ----
EXTENDS Sequences, FiniteSets, Naturals

CONSTANTS Nodes, Root, Procs, Succ

(* Bounded successor relation: each node has exactly two successors. *)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> 
    CASE n = 0 -> {1, 2}
    [] n = 1 -> {2, 3}
    [] n = 2 -> {3, 0}
    [] n = 3 -> {0, 1}
    [] OTHER -> {}]

(* Finite version of Seq, limited by the number of nodes. *)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Include the parallel reachability algorithm specification. *)
INSTANCE ParReach

Spec    == ParReach!Spec
Inv     == ParReach!Inv
Refines == ParReach!Refines
====