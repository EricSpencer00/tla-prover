---- MODULE MC_sums_even ----
EXTENDS Naturals, Integers

CONSTANTS MaxNat, Nat

VARIABLES x
vars == <<x>>

TypeOK == x \in Nat

Init == x = 0

Next == \/ \E k \in Nat : x' = k

Spec == Init /\ [][Next]_vars

Even(n) == \E m \in Nat : n = 2 * m

DoubleEven == Even(2 * x)

====