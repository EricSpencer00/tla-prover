---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The finite override for the natural numbers: the base spec's theorem only
\* needs to be model-checked up to a bounded maximum.
NatOverride == 0..MaxNat

Spec == Init /\ Next

Init == TRUE

Next == TRUE

Invariants == TRUE

Properties == TRUE

====