---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

NatOverride == (0 .. MaxNat)

SPECIFICATION == Init /\ Next

Init == TRUE

Next == TRUE

INVARIANTS == TRUE

Properties == TRUE

====