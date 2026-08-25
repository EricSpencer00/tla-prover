---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

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
  Concrete definitions for parameters expected by ParReach but not
  supplied by the .cfg.  They satisfy the required types but are
  otherwise left uninterpreted.
---------------------------------------------------------------------*)

Marked  == {}                         \* subset of Nodes
Vroot   == FALSE                      \* Boolean flag
ToVroot == {}                         \* set of Nodes (or empty)
PC      == [p \in Procs |-> 0]        \* program counter per process
U       == [p \in Procs |-> Root]    \* selected node per process

(*--------------------------------------------------------------------
  Instantiation of the parallel reachability algorithm
---------------------------------------------------------------------*)

INSTANCE ParReach WITH
    Nodes   <- Nodes,
    Root    <- Root,
    Procs   <- Procs,
    Succ    <- Succ,
    marked  <- Marked,
    vroot   <- Vroot,
    toVroot <- ToVroot,
    pc      <- PC,
    u       <- U

(*--------------------------------------------------------------------
  Specification, invariant and property definitions
---------------------------------------------------------------------*)

Spec    == ParReach!Spec
Init    == ParReach!Init
Next    == ParReach!Next
Inv     == ParReach!Inv
Refines == ParReach!Refines
====