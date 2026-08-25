---- MODULE MCParReach ----
EXTENDS Sequences, Naturals, FiniteSets, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete configuration of the graph and processes *)

Nodes == 1..4

Root == 1

Procs == {"p1", "p2"}

(* Each node has exactly two successors.  This operator will be substituted
   for the constant Succ by the configuration file. *)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      CASE n = 1 -> {2, 3}
      [] n = 2 -> {3, 4}
      [] n = 3 -> {1, 4}
      [] n = 4 -> {1, 2}
  ]

(* A finite version of Seq: sequences over a set S whose length does not
   exceed the number of nodes. *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Specification, invariant and refinement property, delegated to the
   parallel reachability algorithm module. *)
Spec == ParReach!Spec

Inv == ParReach!Inv

Refines == ParReach!Refines

====