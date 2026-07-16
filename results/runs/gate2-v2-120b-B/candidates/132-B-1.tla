------------------------- MODULE MCMajority ----------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers

CONSTANTS A, B, C, bound

(* The bound must be a natural number (including 0). *)
ASSUME bound \in Nat

Value == {A, B, C}

(* Sequences of length 0 up to bound over the set Value. *)
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(* The Majority module defines the core algorithm. We instantiate it with
   the specific set of values and the bound. *)
INSTANCE Majority WITH
    Value  <- Value,
    bound  <- bound,
    seq    <- seq,
    i      <- i,
    cand   <- cand,
    cnt    <- cnt

=============================================================================