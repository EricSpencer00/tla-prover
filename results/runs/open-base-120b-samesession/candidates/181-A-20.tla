---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

\* Initial condition
INIT == n = 0

\* Nondeterministic step: the variable may take any value in the finite natural set
NEXT == n' \in NatOverride

\* Specification of the system
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

\* Definition of evenness using the finite natural set
Even(x) == \E k \in NatOverride : x = 2 * k

\* The theorem to be assumed/checked: the double of any natural number is even
Theorem == \A m \in NatOverride : Even(2 * m)

INVARIANTS == n \in NatOverride

PROPERTIES == Theorem

====