---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete values for the configuration *)
ASSUME Nodes = {"n1", "n2", "n3", "n4"}
ASSUME Root = "n1"
ASSUME Root \in Nodes
ASSUME Procs = {"p1", "p2"}

(* ConnectedToSomeButNotAll replaces Succ in the configuration.
   Each node has exactly two successors, all drawn from Nodes. *)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      CASE n = "n1" -> {"n2", "n3"}
      [] n = "n2" -> {"n3", "n4"}
      [] n = "n3" -> {"n4", "n1"}
      [] n = "n4" -> {"n1", "n2"}
      [] OTHER   -> {}
  ]

(* LimitedSeq replaces Seq from the Sequences module.
   It restricts sequences to length at most the number of nodes. *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Top‑level specification for TLC *)
Spec == ParReach!Spec

(* Inductive invariant *)
Inv == ParReach!Inv

(* Refinement property asserting implementation of the sequential Misra algorithm *)
Refines == ParReach!Refines

====