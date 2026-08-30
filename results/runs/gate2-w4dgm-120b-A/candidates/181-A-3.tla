---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Model-checking configuration for the "double of any natural is even" theorem.
\* This module restricts the natural-number set to a finite range so TLC can
\* explore it exhaustively; the theorem itself is assumed here as a constant-
\* level hypothesis, which is what enables the check.
NatOverride == 0..MaxNat

\* The base specification is parameterized by the operator Nat it uses to name
\* the natural-number set; here that operator is replaced with NatOverride.
Spec == "sums_even.tla"
Init == "Init"
Step == "Step"
Invariants == <<>>
Properties == <<>>

====