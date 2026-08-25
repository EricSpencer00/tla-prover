---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

INIT == n \in NatOverride

NEXT == n' \in NatOverride

Even(x) == x % 2 = 0

DoubleIsEven == \A n \in NatOverride : Even(2 * n)

ASSUME DoubleIsEven

SPECIFICATION == INIT /\ [][NEXT]_<<n>>

INVARIANTS == { DoubleIsEven }

PROPERTIES == { DoubleIsEven }

====