---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete values for the configuration *)
ASSUME Nodes = {"n1", "n2", "n3", "n4"}
ASSUME Root = "n1"
ASSUME Root \in Nodes
ASSUME Procs = {"p1", "p2"}

(* ConnectedToSomeButNotAll replaces Succ in the configuration.
   Each node has exactly two successors, all drawn from Nodes. *)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |
      CASE n = "n1" -> {"n2", "n3"}
      [] n = "n2" -> {"n3", "n4"}
      [] n = "n3" -> {"n4", "n1"}
      [] n = "n4" -> {"n1", "n2"}
      [] OTHER   -> {}
  ]

(* LimitedSeq replaces Seq from the Sequences module.
   It restricts sequences to length at most the number of nodes. *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Instantiate the parallel reachability algorithm with the concrete
   configuration values. *)
INSTANCE ParReach AS PR WITH
  Nodes <- Nodes,
  Root  <- Root,
  Procs <- Procs,
  Succ  <- Succ

(* Top‑level specification for TLC *)
Spec == PR!Spec

(* Inductive invariant *)
Inv == PR!Inv

(* Refinement property asserting implementation of the sequential Misra algorithm *)
Refines == PR!Refines

====