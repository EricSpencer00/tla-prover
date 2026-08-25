---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

(* concrete values for the configuration *)
ASSUME Nodes = 1..4
ASSUME Root = 1
ASSUME Procs = 1..2

(* graph structure: each node has exactly two successors *)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> 
    CASE n = 1 -> {2, 3}
    [] n = 2 -> {3, 4}
    [] n = 3 -> {4, 1}
    [] n = 4 -> {1, 2}
  ]

(* bounded sequence operator for model checking *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* instantiate the parallel reachability algorithm with the concrete constants *)
INSTANCE ParReach WITH 
  Nodes <- Nodes,
  Root  <- Root,
  Procs <- Procs,
  Succ  <- Succ

Init == ParReach!Init
Next == ParReach!Next
Spec == ParReach!Spec
Inv  == ParReach!Inv
Refines == ParReach!Refines

====