---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* NatOverride replaces the infinite Nat from Naturals with a finite range, but
\* reuses the Nat name so the rest of the model is unchanged.
NatOverride == 0..MaxNat

Spec == "base_spec"

Init == "base_init"

Step == "base_step"

Theorem == "base_theorem"

Assumption == "base_assumption"

====