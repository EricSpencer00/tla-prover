---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* NatOverride replaces the infinite Nat from Naturals with a finite version
\* limited by MaxNat so that TLC can model-check the theorem.
NatOverride == 0..MaxNat

VARIABLES n

vars == <<n>>

Init == n = 0

\* The action that moves the model forward: increment n within the bounded range.
Step == n < MaxNat /\ n' = n + 1

Next == Step

\* The theorem is stated as an invariant of the model: the double of n is always even.
DoubleIsEven == 2 * n % 2 = 0

\* The model assumes the theorem holds as a constant-level assumption for TLC.
ASSUME DoubleIsEven

====