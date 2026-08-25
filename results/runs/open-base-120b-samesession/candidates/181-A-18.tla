---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* Evenness predicate
Even(n) == n % 2 = 0

VARIABLE n

\* Initial state: pick any natural number from the finite set
Init == n \in NatOverride

\* Next-state relation: any value from the finite set may be chosen
Next == n' \in NatOverride

\* Standard specification decomposition
SPECIFICATION == Init /\ [][Next]_<<n>>

\* Required identifiers exposed for the .cfg file
INIT == Init
NEXT == Next
INVARIANTS == Even(2 * n)
PROPERTIES == \A m \in NatOverride : Even(2 * m)

====