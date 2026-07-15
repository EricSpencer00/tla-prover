------------------------- MODULE MCMajority ----------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS A, B, C, bound

(* The bound must be a natural number (i.e., a non‑negative integer). *)
ASSUME bound \in Nat

Value == {A, B, C}

(* Sequences of elements from S whose length does not exceed the bound. *)
BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

(* Include the definitions of the auxiliary module that implements the
   majority‑vote algorithm. *)
INSTANCE Majority

=============================================================================