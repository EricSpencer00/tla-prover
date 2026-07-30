---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

NatOverride == { n \in Nat : n <= MaxNat }

Specification == TRUE
Init == TRUE
Next == TRUE
INVARIANTS == TRUE
Properties == TRUE

====