---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The usual infinite Nat set is replaced here with a finite range for model
\* checking; the replacement must keep the name Nat so inherited definitions
\* keep working.
NatOverride == 0..MaxNat

\* The theorem (double of any natural is even) is assumed here as a constant
\* fact for TLC; the override above is what makes the state space finite.
ASSUME \A n \in NatOverride : (2 * n) % 2 = 0

Spec == TRUE
Init == TRUE
Next == TRUE
TypeOK == TRUE
StateConstraint == TRUE
BoundState == TRUE

====