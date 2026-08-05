---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

NatOverride == 0..MaxNat

ASSUME Nat = NatOverride

Spec == TRUE
Init == TRUE
Next == TRUE

====