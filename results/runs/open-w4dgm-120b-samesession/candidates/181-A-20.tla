---- MODULE MC_sums_even ----
EXTENDS Naturals, Integers

CONSTANTS MaxNat

\* Finite replacement for the unbounded Nat from Naturals, enabling model checking.
NatOverride == 0..MaxNat

SpecAssumption == \E x \in NatOverride : (2 * x) % 2 = 0

TypeOK == MaxNat \in NatOverride

Spec == SpecAssumption

====