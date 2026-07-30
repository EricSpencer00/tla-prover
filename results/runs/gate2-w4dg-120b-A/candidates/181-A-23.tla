---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

VARIABLES x

vars == << x >>

TypeOK == x \in Nat

Init == x = 0

Next == \E y \in Nat : x' = y

Spec == Init /\ [][Spec]_vars

Even == \E k \in Nat : x = 2 * k

====