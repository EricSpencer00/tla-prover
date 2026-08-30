---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Overrides the infinite Nat set from Naturals with a finite range for TLC.
NatOverride == 0..MaxNat

\* Theorem from the base specification (assumed as a constant-level fact for
\* model checking): double a number is even.
Theorem == \A n \in NatOverride : (2 * n) % 2 = 0

Spec == Init /\ Next

Init == TRUE

Next == TRUE

Invariants == {}

Properties == {}
====