---- MODULE MC_sums_even ----
EXTENDS Naturals, Integers

CONSTANT MaxNat

NatOverride == 0 .. MaxNat

VARIABLES value, double, increment

vars == <<value, double, increment>>

Spec == Init /\ [][Next]_vars

Init ==
    /\ value = 0
    /\ double = 0
    /\ increment = 1

Next ==
    \/ \E k \in NatOverride :
         /\ value' = k
         /\ double' = 2 * k
         /\ increment' = IF increment = 1 THEN 2 ELSE 1
    \/ UNCHANGED vars

DoubleIsEven == double % 2 = 0

TheoremEvenDouble == TRUE

====