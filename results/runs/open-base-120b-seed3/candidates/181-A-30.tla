---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

INIT == n \in NatOverride

NEXT == UNCHANGED n

SPECIFICATION == INIT /\ [][NEXT]_<<n>>

IsEven(x) == \E k \in NatOverride : x = 2 * k

Theorem == \A n \in NatOverride : IsEven(2 * n)

INVARIANTS == Theorem

PROPERTIES == Theorem
====