---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete configuration for model checking *)
ASSUME Nodes = {1, 2, 3, 4}
ASSUME Root  = 1
ASSUME Procs = {1, 2}
(* Each node has exactly two successors *)
ASSUME Succ = {
  <<1, 2>>, <<1, 3>>,
  <<2, 3>>, <<2, 4>>,
  <<3, 1>>, <<3, 4>>,
  <<4, 1>>, <<4, 2>>
}

(* Operator substituted for Succ in the configuration *)
ConnectedToSomeButNotAll(node) == { m \in Nodes : <<node, m>> \in Succ }

(* Finite version of Seq, bounded by the number of nodes *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Import the parallel reachability algorithm specification *)
INSTANCE ParReach WITH
  Nodes <- Nodes,
  Root  <- Root,
  Procs <- Procs,
  Succ  <- Succ

Spec    == ParReach!Spec
Inv     == ParReach!Inv
Refines == ParReach!Refines

====