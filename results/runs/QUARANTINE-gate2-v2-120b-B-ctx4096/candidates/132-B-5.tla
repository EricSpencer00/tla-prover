------------------------- MODULE MCMajority ----------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* The original specification incorrectly asserted that `bound` is NOT a natural
   number, which makes the model impossible to instantiate.  We replace that
   assumption with a correct one that states `bound` is a natural number.
   This preserves the intended meaning (the bound is a non‑negative integer) *)
ASSUME bound \in Nat

Value == {A, B, C}

(* Sequences of elements taken from `Value` whose length is between 0 and
   `bound` inclusive. *)
BoundedSeq(S) == { s \in [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(* Include the majority‑vote algorithm definitions *)
INSTANCE Majority

=============================================================================