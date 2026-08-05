---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

NatOverride == 0 .. MaxNat

VARIABLES n

vars == << n >>

Init == n = 0

DoubleStep == n' = n + n

Next == DoubleStep

TypeOK == n \in NatOverride

TheoremStatement == \A k \in NatOverride : k + k \in NatOverride /\ (k + k) % 2 = 0

====