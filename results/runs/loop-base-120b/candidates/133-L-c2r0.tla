---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(*--------------------------------------------------------------------
  Concrete configuration for model checking
---------------------------------------------------------------------*)

(* The set of graph nodes (exactly 4) *)
Nodes == {"n1", "n2", "n3", "n4"}

(* The designated start node *)
Root == "n1"

(* The set of worker processes (exactly 2) *)
Procs == {"p1", "p2"}

(* Successor relation: each node has exactly two successors *)
Succ == [
    "n1" |-> {"n2", "n3"},
    "n2" |-> {"n3", "n4"},
    "n3" |-> {"n4", "n1"},
    "n4" |-> {"n1", "n2"}
]

(*--------------------------------------------------------------------
  Operators required by the .cfg substitution
---------------------------------------------------------------------*)

(* The configuration substitutes this operator for Succ.
   Here we simply reuse the concrete Succ defined above; any
   additional filtering required by a particular experiment can be
   added without changing the rest of the model. *)
ConnectedToSomeButNotAll == Succ

(* Bounded version of the standard Seq operator.
   Sequences are limited to length at most |Nodes|, ensuring a
   finite state space for model checking. *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*--------------------------------------------------------------------
  Specification, invariant and property definitions
---------------------------------------------------------------------*)

(* The overall behavior of the parallel reachability algorithm,
   instantiated with the concrete constants above. *)
Spec == ParReach!Spec

Init == ParReach!Init
Next == ParReach!Next

(* Inductive invariant used for safety checking *)
Inv == ParReach!Inv

(* Refinement property asserting correspondence with the sequential
   Misra algorithm *)
Refines == ParReach!Refines

====