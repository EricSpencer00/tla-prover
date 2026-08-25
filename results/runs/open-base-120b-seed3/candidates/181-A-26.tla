---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

\* Initial condition: n is any natural in the finite range
Init == n \in NatOverride

\* Next-state relation: nondeterministically choose any n' in the range
Next == n' \in NatOverride

\* Full specification
Spec == Init /\ [][Next]_<<n>>

\* Helper definition: evenness
IsEven(x) == x % 2 = 0

\* Assumed theorem (constant‑level assumption for TLC)
Theorem == \A m \in NatOverride : IsEven(2 * m)

\* Required identifiers
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == Theorem
PROPERTIES == Theorem
====