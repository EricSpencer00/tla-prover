---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

NatOverride == 0 .. MaxNat

THEOREM_EVEN_DOUBLE == \A n \in NatOverride : (2 * n) % 2 = 0

====