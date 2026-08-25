---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

\* Assume the theorem that the double of any natural number is even
ASSUME DoubleIsEven ==
    \A m \in NatOverride : \E k \in NatOverride : 2 * m = 2 * k

VARIABLE n

Init == n = 0

Next == n' = n

SPECIFICATION == Init /\ [][Next]_<<n>>

INVARIANTS == {}

PROPERTIES == {}

====