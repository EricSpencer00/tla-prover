---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

\* Definition of evenness using the finite NatOverride
Even(x) == ∃ k \in NatOverride : x = 2 * k

\* The theorem we assume holds for all numbers in the bounded range
Theorem == ∀ n \in NatOverride : Even(2 * n)

ASSUME Theorem

VARIABLES n

INIT == n \in NatOverride

NEXT == /\ n' \in NatOverride

SPECIFICATION == INIT /\ [][NEXT]_n

INVARIANTS == Theorem

PROPERTIES == Theorem
====