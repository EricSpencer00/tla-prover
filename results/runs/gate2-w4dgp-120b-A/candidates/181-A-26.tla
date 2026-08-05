---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

NatOverride == 0 .. MaxNat

SumOfDouble ==
  \A n \in NatOverride : (2 * n) % 2 = 0

====