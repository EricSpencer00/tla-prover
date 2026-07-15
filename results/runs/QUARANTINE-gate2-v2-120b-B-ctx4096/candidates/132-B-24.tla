---- MODULE MCMajority -----------------------------------------------

EXTENDS Integers

CONSTANTS A, B, C, bound

\* Ensure that A, B, and C are distinct elements of the natural numbers.
\* This is required for the Majority instance to work correctly.
ASSUME A \in Nat /\ B \in Nat /\ C \in Nat /\ A # B /\ A # C /\ B # C

\* Ensure that the bound is a natural number (the maximum sequence length).
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

INSTANCE Majority

=============================================================================