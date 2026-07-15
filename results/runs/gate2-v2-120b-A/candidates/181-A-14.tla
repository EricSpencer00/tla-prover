---- MODULE MC_sums_even ----
EXTENDS Naturals, FiniteSets

CONSTANT MaxNat
VARIABLE n

\* Override the infinite set of natural numbers with a finite range
Nat == 0 .. MaxNat

\* State predicate asserting that the current number is within the finite range
State == n \in Nat

\* Initial state: start from any natural number in the finite range
Init == n \in Nat

\* No state changes; the system is static for model checking
Next == UNCHANGED n

\* Specification combining the initial predicate and the step relation
Spec == Init /\ [][Next]_<<n>>

\* Safety property: the double of any natural number is even
DoubleEven == (2 * n) % 2 = 0

\* Invariant (optional) mirroring the safety property
Invariant == DoubleEven

\* Property (optional) mirroring the safety property
Property == DoubleEven

=============================================================================