---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

NatOverride == 0 .. MaxNat

ASSUME Nat = NatOverride

THEOREM_EVEN_DOUBLING ==
    \A n \in Nat : n + n \in {m \in Nat : \E p \in Nat : m = 2 * p}

====