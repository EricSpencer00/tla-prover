---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(*--------------------------------------------------------------------
  Concrete definitions required for model checking
--------------------------------------------------------------------*)

(* The set of nodes in the graph (4 nodes) *)
Nodes == 1..4

(* The root node of the graph *)
Root == 1

(* The set of worker processes (2 processes) *)
Procs == 1..2

(*--------------------------------------------------------------------
  Bounded graph structure: each node has exactly two successors.
  This operator will be substituted for the generic Succ operator.
--------------------------------------------------------------------*)
ConnectedToSomeButNotAll ==
    [ n \in Nodes |-> 
        CASE n = 1 -> {2, 3}
        []  n = 2 -> {3, 4}
        []  n = 3 -> {4, 1}
        []  n = 4 -> {1, 2}
    ]

(*--------------------------------------------------------------------
  Bounded version of Seq for finite‑state model checking.
  This operator replaces the standard Seq operator.
--------------------------------------------------------------------*)
LimitedSeq(S) ==
    { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*--------------------------------------------------------------------
  Specification, invariant and refinement property inherited from the
  parallel reachability algorithm.
--------------------------------------------------------------------*)
Spec == ParReach!Spec
Inv  == ParReach!Inv
Refines == ParReach!Refines

====