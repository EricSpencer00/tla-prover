---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

\* Initial state: n ranges over the finite natural numbers
Init == n \in NatOverride

\* No state changes; the property is checked on the initial state
Next == UNCHANGED n

\* Specification combining Init and Next
Spec == Init /\ [][Next]_<<n>>

\* Helper definition: a number is even if it is twice some natural
IsEven(x) == \E k \in NatOverride : x = 2 * k

\* The theorem we wish to check: double of any natural is even
Theorem == \A m \in NatOverride : IsEven(2 * m)

\* Required identifiers
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == Theorem
PROPERTIES == Theorem

====