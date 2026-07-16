---- MODULE MCMajority ----
EXTENDS Integers, Sequences, FiniteSets, Majority

(***************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all    *)
(* sequences over three elements of bounded length.                        *)
(***************************************************************************)

CONSTANTS A, B, C, bound

(* bound must be a natural number (including 0) *)
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(* Helper: the set of non‑empty prefixes of a sequence *)
NonEmptyPrefixes(s) == { t \in (0 .. Len(s)) -> Value : t # <<>> }

=============================================================================