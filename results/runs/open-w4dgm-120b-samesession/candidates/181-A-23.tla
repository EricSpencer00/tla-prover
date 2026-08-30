---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* This override is what makes the infinite natural-number set
\* finite for the TLC run; the rest of the proof comes from the base
\* module, whose theorem is assumed here as a constant-level fact.
NatOverride == 0..MaxNat

TheoremDoubleIsEven == \A n \in NatOverride : (2 * n) % 2 = 0

Spec == TRUE
Init == TRUE
Next == TRUE
Vars == {}
StateConstraint == TRUE
TypeOK == TRUE
Invars == {}
Properties == TheoremDoubleIsEven
====