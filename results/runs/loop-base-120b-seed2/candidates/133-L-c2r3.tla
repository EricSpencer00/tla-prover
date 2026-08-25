---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS Nodes, Root, Procs, Succ

(* Finite successor relation: each node can reach any other node except itself. *)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> { s \in Nodes : s # n }]

(* Bounded sequences: length at most the number of nodes. *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Concrete definitions required by ParReach *)
vroot == Root
toVroot == {Root}
pc == [p \in Procs |-> 0]
u == Nodes \ {Root}

(* Import the parallel reachability algorithm, supplying the concrete
   constants and the finite successor relation defined above. *)
INSTANCE ParReach WITH
  Nodes   <- Nodes,
  Root    <- Root,
  Procs   <- Procs,
  Succ    <- ConnectedToSomeButNotAll,
  vroot   <- vroot,
  toVroot <- toVroot,
  pc      <- pc,
  u       <- u

(* Export the required top-level identifiers for the configuration. *)
Spec == ParReach!Spec
Inv == ParReach!Inv
Refines == ParReach!Refines
====