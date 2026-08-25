---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

INIT == n \in NatOverride

NEXT == /\ n' \in NatOverride
        /\ (n' = n + 1 \/ n' = n)

SPECIFICATION == INIT /\ [][NEXT]_<<n>>

INVARIANTS == \A m \in NatOverride : \E k \in NatOverride : 2 * m = 2 * k

PROPERTIES == INVARIANTS
====