---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

\* Initial state: any natural number within the bounded range
Init == n \in NatOverride

\* Transition: iterate through the bounded range (wrap around at MaxNat)
Next == 
    /\ n \in NatOverride
    /\ n' = IF n = MaxNat THEN 0 ELSE n + 1

\* State predicate expressing that the double of n is even
DoubleEven == (2 * n) % 2 = 0

\* Full specification required by the .cfg
SPECIFICATION == Init /\ [][Next]_<<n>>

\* Operators required by the .cfg (exact names)
INIT == Init
NEXT == Next
INVARIANTS == DoubleEven
PROPERTIES == DoubleEven

====