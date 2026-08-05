---- MODULE MCMajority
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                          *)
(****************************************************************************)
EXTENDS Integers
CONSTANTS A, B, C, bound
\* A true bound is required; a Nat constant (including zero) satisfies it.
ASSUME bound \notin Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

INSTANCE Majority

==============================================================================