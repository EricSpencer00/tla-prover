---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

NatOverride == 0 .. MaxNat

ASSUME FiniteNat == NatOverride

SpecTheorem == \A x \in NatOverride : (x + x) % 2 = 0

====