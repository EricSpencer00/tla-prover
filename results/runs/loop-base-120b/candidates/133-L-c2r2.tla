---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Procs, Succ,
          n1, n2, n3, n4,
          p1, p2

(*--------------------------------------------------------------------
  Operators required by the .cfg substitution
---------------------------------------------------------------------*)

(* The configuration substitutes this operator for Succ.
   It simply returns the successors of a node according to the
   (constant) Succ function. *)
ConnectedToSomeButNotAll(node) == Succ[node]

(* Bounded version of the standard Seq operator.
   Sequences are limited to length at most |Nodes|, ensuring a
   finite state space for model checking. *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*--------------------------------------------------------------------
  Instantiation of the parallel reachability algorithm
---------------------------------------------------------------------*)

(* Bind the concrete constants of this configuration to the
   parameters of ParReach. *)
INSTANCE ParReach WITH
    Nodes <- Nodes,
    Root  <- Root,
    Procs <- Procs,
    Succ  <- Succ

(*--------------------------------------------------------------------
  Specification, invariant and property definitions
---------------------------------------------------------------------*)

(* Expose the main components of the instantiated algorithm. *)
Spec    == ParReach!Spec
Init    == ParReach!Init
Next    == ParReach!Next
Inv     == ParReach!Inv
Refines == ParReach!Refines
====