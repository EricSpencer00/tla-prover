---- MODULE MCMajority ----
EXTENDS Integers
CONSTANTS A, B, C, bound
ASSUME bound \notin Nat

Value == {A,B,C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

INSTANCE Majority

=============================================================================