---- MODULE MC_sums_even ----
EXTENDS Integers, TLC

CONSTANTS MaxNat, Nat

VARIABLE n

Init == n = 0

Next == n' = n

Spec == Init /\ [] [Next]_n

EvenDouble == \A i \in Nat : (2*i) % 2 = 0

SPECIFICATION == Spec

INIT == Init

NEXT == Next

INVARIANTS == EvenDouble

PROPERTIES == {}

====