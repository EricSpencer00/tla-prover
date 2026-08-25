---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

\* Initial state: start at 0
INIT == n = 0

\* Transition: increment while staying within the bound, or stutter
NEXT == 
    \/ /\ n < MaxNat
       /\ n' = n + 1
    \/ /\ n' = n

\* Full specification
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

\* Definition of evenness using the finite NatOverride
Even(m) == \E k \in NatOverride : m = 2 * k

\* Invariant stating that double of any natural in the range is even
Invariant == \A x \in NatOverride : Even(2 * x)

INVARIANTS == Invariant
PROPERTIES == Invariant
====