---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

VARIABLES n

vars == << n >>

TypeOK == n \in Nat

Init == n = 0

Next == n < MaxNat /\ n' = n + 1 /\ UNCHANGED << >>

Spec == Init /\ [][Next]_vars

Theorem == \A n \in Nat : (2 * n) % 2 = 0

====