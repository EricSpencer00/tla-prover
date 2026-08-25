---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

\* Initial state: n ranges over the finite naturals
Init == n \in NatOverride

\* No state changes; the model is static
Next == UNCHANGED n

\* Full specification
SPECIFICATION == Init /\ [][Next]_<<n>>

\* Definition of evenness using the finite NatOverride
IsEven(m) == \E k \in NatOverride : m = 2 * k

\* Theorem (assumed true) that the double of any natural is even
THEOREM == \A n \in NatOverride : IsEven(2 * n)

\* Invariant to be checked by TLC
INVARIANTS == { IsEven(2 * n) }

\* No additional temporal properties
PROPERTIES == {}

====