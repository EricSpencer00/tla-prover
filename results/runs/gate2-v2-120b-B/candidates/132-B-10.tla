---- MODULE MCMajority ----
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS A, B, C, bound

(* Corrected assumption: \"bound\" is a natural number (including 0). *)
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

(* The algorithm from Majority.tla is used. *)
INSTANCE Majority

=============================================================================