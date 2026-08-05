---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

NatOverride == 0..MaxNat

ASSUME MaxNat \in Nat /\ MaxNat >= 1

Even(n) == \E m \in Nat : n = 2 * m

====