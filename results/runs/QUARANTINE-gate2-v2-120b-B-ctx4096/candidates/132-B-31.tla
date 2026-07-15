---- MODULE MCMajority ----
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS A, B, C, bound

(*
  The original specification asserted that `bound` is *not* a natural number,
  which caused SANY to reject the module (the assumption is false when a
  concrete natural number is supplied in the cfg).  The intent of the module
  is to bound the length of the sequences that are examined, so `bound`
  must be a natural number.  We therefore replace the incorrect assumption
  with a correct one that preserves the intended semantics.
*)
ASSUME bound \in Nat

Value == {A, B, C}

(*
  BoundedSeq(S) is the set of all finite sequences over the set S whose
  length does not exceed the constant `bound`.  The definition uses the
  standard Sequences module.
*)
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

=============================================================================