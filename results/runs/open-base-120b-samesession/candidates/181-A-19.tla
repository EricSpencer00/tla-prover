---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

INIT == n \in NatOverride

NEXT == UNCHANGED n

SPECIFICATION == INIT /\ [][NEXT]_<<n>>

Even(m) == \E k \in NatOverride : m = 2 * k

INVARIANTS == \A n \in NatOverride : Even(2 * n)

PROPERTIES == INVARIANTS
====