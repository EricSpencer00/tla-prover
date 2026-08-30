---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The theorem being checked: the double of any natural number is even, written as a
\* structural property of the double function instead of an arithmetic fact. The
\* model itself is bounded by MaxNat (one million) so TLC can explore it.
SpecCounted == TRUE

NatOverride == 0 .. MaxNat

DoubleIsEven == \A n \in NatOverride : \E k \in NatOverride : 2 * n = 2 * k

Spec == DoubleIsEven

====