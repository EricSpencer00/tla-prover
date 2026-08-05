---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

NatOverride == 0 .. MaxNat

ASSUME MaxNat \in Nat /\ MaxNat >= 1

THEOREM_FORALL_NAT_DOUBLE_IS_EVEN ==
    \A n \in NatOverride : 2 * n % 2 = 0

====