---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

NatOverride == 0 .. MaxNat

VARIABLES n

vars == << n >>

TypeOK ==
    /\ n \in NatOverride

Init ==
    /\ n = 0

Next ==
    /\ \E k \in NatOverride : n' = k

Spec == Init /\ [][Next]_vars

DoubleEven ==
    \A n \in NatOverride : (2 * n) % 2 = 0

====