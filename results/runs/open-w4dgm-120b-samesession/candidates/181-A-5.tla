---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Overridden finite natural-number set for the model check (replaces Naturals.Nat).
NatOverride == 0..MaxNat

\* The theorem that double of any natural is even is assumed here as a constant-level
\* fact, so the model can focus on the overridden finite range.
TheoremEvenDouble == \A n \in NatOverride : (2 * n) % 2 = 0

Spec == TRUE
Init == TRUE
Next == TRUE
TypeOK == TRUE
StateConstraint == TRUE
StateConstraint == TRUE

INVARIANT TypeOK
INVARIANT StateConstraint
PROPERTY TheoremEvenDouble
====