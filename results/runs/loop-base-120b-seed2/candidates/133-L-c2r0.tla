---- MODULE MCParReach ----
EXTENDS Naturals, Sequences
CONSTANTS Nodes, Root, Procs, Succ

(* Finite successor relation: each node can reach any other node except itself.
   This satisfies the requirement that Succ be replaced by a finite operator. *)
ConnectedToSomeButNotAll == 
  [n \in Nodes |-> { s \in Nodes : s # n }]

(* Bounded sequences: length at most the number of nodes. *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Import the parallel reachability algorithm, supplying the concrete
   constants and the finite successor relation defined above. *)
INSTANCE ParReach WITH
  Nodes <- Nodes,
  Root  <- Root,
  Procs <- Procs,
  Succ  <- ConnectedToSomeButNotAll

(* Specification and properties required by the .cfg file. *)
Spec    == ParReach!Spec
Inv     == ParReach!Inv
Refines == ParReach!Refines

====