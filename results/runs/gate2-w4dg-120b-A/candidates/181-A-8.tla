---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

VARIABLES n
vars == << n >>

TypeOK == n \in Nat

Init == n = 0

Next == \E m \in Nat : n' = m

Spec == Init /\ [][Next]_vars

DoublesAreEven == (2 * n) % 2 = 0

====