---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

VARIABLES n

\* Initial state: choose any natural number within the finite range
Init == n \in NatOverride

\* No state changes; the system is static
Next == UNCHANGED n

\* Full specification of the system
Spec == Init /\ [][Next]_<<n>>

\* The theorem: the double of any natural number is even
EvenDouble == \A m \in NatOverride : (2 * m) % 2 = 0

\* Required identifiers for the configuration module
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == EvenDouble
PROPERTIES == EvenDouble

====