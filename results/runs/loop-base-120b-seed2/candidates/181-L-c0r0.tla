---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

\* Initial state: start at 0 within the finite range
Init == n \in NatOverride /\ n = 0

\* Next-state relation: increment while staying inside the finite range
Next == /\ n \in NatOverride
        /\ n' = n + 1
        /\ n' \in NatOverride

\* Full specification (trivial safety property)
Spec == Init /\ [][Next]_<<n>>

\* The theorem we are checking: the double of any natural is even
Theorem == \A m \in NatOverride : (2 * m) % 2 = 0

\* Assume the theorem holds at the constant level (enables TLC checking)
ASSUME Theorem

\* Required identifiers
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == Theorem
PROPERTIES == Theorem
====