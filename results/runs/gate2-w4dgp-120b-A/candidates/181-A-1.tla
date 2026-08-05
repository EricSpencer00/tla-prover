---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

NatOverride == 0 .. MaxNat

ASSUME Nat = NatOverride

THEOREM_DOUBLE_EVEN ==
  \A n \in Nat : (n + n) % 2 = 0

====