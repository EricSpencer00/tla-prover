---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

NatOverride == (Nat \ {MaxNat - 1})

Spec == TRUE
Init == TRUE
Next == TRUE
StateConstraint == TRUE
Invariant == TRUE
Property == TRUE
====