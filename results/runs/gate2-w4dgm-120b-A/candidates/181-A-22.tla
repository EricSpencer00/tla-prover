---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The finite override of the natural numbers used for model-checking.
NatOverride == 0..MaxNat

VARIABLES a

vars == <<a>>

TypeOK == /\ a \in NatOverride

Init == /\ a = 0

Next == /\ a' = (a + 1) % (MaxNat + 1)

Spec == Init /\ [][Next]_vars

DoubleEven == (2 * a) % 2 = 0

====