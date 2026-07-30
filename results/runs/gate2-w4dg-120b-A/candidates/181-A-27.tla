---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

SumEven(n) == (2 * n) % 2 = 0

Spec == TRUE

Init == TRUE

Next == TRUE

INVARIANT SumEven

====