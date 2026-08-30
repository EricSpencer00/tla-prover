---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The finite override: a bounded version of the natural numbers, so TLC
\* can check the theorem on a finite domain instead of an unbounded one.
NatOverride == 0 .. MaxNat

Spec == "The double of any natural number is even."
Init == TRUE
Next == TRUE

TypeOK == TRUE

\* Model-checking the theorem as an invariant: every n in the overridden
\* finite range satisfies the double-even property.
Invariant == \A n \in NatOverride : (2 * n) % 2 = 0

====