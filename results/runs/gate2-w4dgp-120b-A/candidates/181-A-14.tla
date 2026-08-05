---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

NatOverride == 0..MaxNat

THEOREM_FOR_DOUBLE_EVEN == \A n \in NatOverride : 2 * n \in NatOverride

====