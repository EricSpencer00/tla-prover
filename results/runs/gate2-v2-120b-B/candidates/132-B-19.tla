------------------------- MODULE MCMajority -------------------------------
EXTENDS Integers

(*----------------------------------------------------------------------
  This module provides a concrete bound for the majority vote algorithm.
  It imports the abstract algorithm from the Majority module and supplies
  a finite set of possible values together with a maximum sequence length.
----------------------------------------------------------------------*)

CONSTANTS A, B, C, bound

(* The bound must be a natural number (non‑negative integer). *)
ASSUME bound \in Nat

(* The set of possible values that may appear in a sequence. *)
Value == {A, B, C}

(* All finite sequences (functions from 1..n) whose elements are drawn
   from Value, where the length n ranges from 0 up to the specified bound. *)
BoundedSeq(S) == UNION { [i \in 1..n |-> v] :
                          n \in 0..bound,
                          v \in [1..n -> S] }

(* Export the bound and the set of values for use by the Majority module. *)
VARIABLES seq, i, cand, cnt

INSTANCE Majority WITH
    bound <- bound,
    Value <- Value

=============================================================================