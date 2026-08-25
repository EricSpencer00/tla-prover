---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* Assumed theorem: the double of any natural number in the bounded range is even
ASSUME Theorem == \A n \in NatOverride : (2 * n) % 2 = 0

\* Trivial state since the property is purely arithmetic
Init == TRUE
Next == TRUE

SPECIFICATION == Init /\ [][Next]_<<>>
INIT == Init
NEXT == Next
INVARIANTS == Theorem
PROPERTIES == Theorem
====