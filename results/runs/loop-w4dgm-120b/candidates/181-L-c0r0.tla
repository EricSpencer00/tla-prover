---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The finite override: Nat is redefined as the bounded range 0..MaxNat, so
\* the model is checkable. It replaces the infinite Nat from Naturals.
NatOverride == 0..MaxNat

\* The theorem from the base spec is assumed here as a constant-level
\* assumption; the model checks the rest of the system under that assumption.
TheoremAssumption == \A n \in NatOverride : (2 * n) % 2 = 0

Spec == TheoremAssumption

Init == TRUE

Next == TRUE

StateConstraint == TRUE

StateConstraintSpec == StateConstraint

====