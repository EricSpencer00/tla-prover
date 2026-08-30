---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* NatOverride replaces the infinite Nat from Naturals with a finite range
\* so TLC can check the model; it is defined here and not declared.
NatOverride == 0..MaxNat

\* The theorem from the base specification is assumed here as a constant-level
\* assumption for model checking; it is not proved in this module.
THEOREM_DOUBLE_EVEN == \A n \in NatOverride : (2 * n) % 2 = 0

Spec == TRUE
Init == TRUE
Next == TRUE
Invariants == {}
Properties == {THEOREM_DOUBLE_EVEN}
====