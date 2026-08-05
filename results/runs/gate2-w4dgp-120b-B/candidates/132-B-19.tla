---- MODULE MCMajority -----------------------------------------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm over three      *)
(* elements, for all sequences up to a bounded length.                        *)
(*                                                                          *)
(* The `bound` constant is the max sequence length checked.  It must be a     *)
(* natural number, so the module's only real assumption is that `bound \in Nat`. *)
(* The original spec accidentally used `bound \notin Nat`, which makes the   *)
(* model unsatisfiable and blocks TLC.                                       *)
(****************************************************************************)
EXTENDS Integers
CONSTANTS A, B, C, bound
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

INSTANCE Majority
==============================================================================