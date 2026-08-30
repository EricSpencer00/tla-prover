---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* NatOverride replaces the infinite Nat from Naturals with a finite 0..MaxNat
NatOverride == 0..MaxNat

AssumeTheorem == (2 \in NatOverride => \E k \in NatOverride : 2 = 2 * k)

Spec == AssumeTheorem

Init == AssumeTheorem

Next == AssumeTheorem

Invars == Assumptions

Props == Assumptions

====