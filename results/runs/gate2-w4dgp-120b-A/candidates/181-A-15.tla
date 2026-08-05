---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

NatOverride == 0..MaxNat

ASSUME MaxNat >= 1 /\ MaxNat % 2 = 0

VARIABLES x

vars == <<x>>

Init == x = 0

DoubleEvenStep == x < MaxNat /\ x' = x + 2

LastStep == x = MaxNat /\ x' = 0

Next == DoubleEvenStep \/ LastStep

Spec == Init /\ [][Next]_vars

TypeOK == x \in NatOverride

DoubleEven == x % 2 = 0

====