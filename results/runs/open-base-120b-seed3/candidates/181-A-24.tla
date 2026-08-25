---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

VARIABLE n

\* Finite version of the natural numbers, limited by MaxNat
NatOverride == { i \in Nat : i <= MaxNat }

\* Initial state: n is any natural number within the finite range
Init == n \in NatOverride

\* Next-state relation: nondeterministically choose a new n in the finite range
Next == /\ n' \in NatOverride
        /\ UNCHANGED << >>

\* Overall specification
Spec == Init /\ [Next]_<<n>>

SPECIFICATION == Spec
INIT == Init
NEXT == Next

\* The theorem to be checked: the double of any natural number is even
EvenDouble == \A m \in NatOverride : (2 * m) % 2 = 0

INVARIANTS == EvenDouble
PROPERTIES == EvenDouble
====