---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete domain of nodes and processes *)
Nodes == 1..4
Root  == 1
Procs == {"P1", "P2"}

(* Bounded version of Seq for model checking *)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Graph successor function: each node has exactly two successors *)
ConnectedToSomeButNotAll(n) ==
  LET nxt  == (n % Cardinality(Nodes)) + 1
      nxt2 == ((n + 1) % Cardinality(Nodes)) + 1
  IN { nxt, nxt2 }

(* Succ is defined to be the above bounded successor relation *)
Succ == ConnectedToSomeButNotAll

(* Instantiate the parallel reachability algorithm specification *)
INSTANCE ParReachAlg WITH
  Nodes <- Nodes,
  Root  <- Root,
  Procs <- Procs,
  Succ  <- Succ

(* Export the required identifiers *)
Spec    == ParReachAlg!Spec
Inv     == ParReachAlg!Inv
Refines == ParReachAlg!Refines

====