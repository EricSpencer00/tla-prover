---- MODULE MC_sums_even ----
EXTENDS Naturals, FiniteSets

CONSTANT MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* State variable (chosen arbitrarily for the purpose of a complete spec)
VARIABLE n

\* Initialization: n ranges over the finite natural numbers
Init == n \in NatOverride

\* Next-state relation: n may take any value in the finite range
Next == n' \in NatOverride

\* Specification of the system
SPECIFICATION == Init /\ [][Next]_<<n>>

\* Required identifiers for the configuration module
INIT == Init
NEXT == Next

\* Definition of "evenness"
Even(m) == \E k \in NatOverride : m = 2 * k

\* Invariant (and property) stating that double of any natural number is even
PROPERTIES == \A n \in NatOverride : Even(2 * n)

INVARIANTS == PROPERTIES
====