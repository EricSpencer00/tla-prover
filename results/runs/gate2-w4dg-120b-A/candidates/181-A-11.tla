---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

ASSUME MaxNat \in Nat

VARIABLES n

vars == <<n>>

TypeOK == n \in Nat

Init == n = 0

Step == n' = (n + 1) % (MaxNat + 1)

Next == Step

Spec == Init /\ [][Next]_vars

DoubleEven == (2 * n) % 2 = 0

====