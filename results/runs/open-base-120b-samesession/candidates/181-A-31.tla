---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

\* Initial state: n is 0 and within the finite natural numbers
Init == /\ n = 0
        /\ n \in NatOverride

\* Next-state relation: n may take any value in the finite natural numbers
Next == /\ n' \in NatOverride

\* Full specification
Spec == Init /\ [][Next]_<<n>>

\* Theorem (assumed true): the double of any natural number is even
EvenDouble == \A m \in NatOverride : \E k \in Nat : 2 * m = 2 * k

\* Required identifiers
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == EvenDouble
PROPERTIES == EvenDouble
====