---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

(* concrete definitions for the constants *)
ASSUME Nodes = {1, 2, 3, 4}
ASSUME Root  = 1
ASSUME Procs = {"p1", "p2"}

(* operator that will replace Succ in the configuration *)
ConnectedToSomeButNotAll(node) ==
  CASE node = 1 -> {2, 3}
   [] node = 2 -> {3, 4}
   [] node = 3 -> {4, 1}
   [] node = 4 -> {1, 2}

(* a finite version of Seq, limited by the number of nodes *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* instantiate the parallel reachability algorithm without bringing its
   operators directly into this namespace *)
INSTANCE ParReach AS PR

(* expose the main specification, invariant, and refinement property from ParReach *)
Spec == PR!Spec
Inv == PR!Inv
Refines == PR!Refines
====