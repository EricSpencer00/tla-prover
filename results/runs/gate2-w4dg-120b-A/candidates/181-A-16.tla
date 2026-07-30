---- MODULE MC_sums_even ----
EXTENDS Integers

CONSTANTS MaxNat, Nat

ASSUME MaxNat \in Nat \ {0}

VARIABLES n

vars == << n >>

TypeOK == n \in Nat

Init == n = 0

Next == \E m \in Nat : n' = m

Spec == Init /\ [][Next]_vars

EvenDouble == 2 * n % 2 = 0

====