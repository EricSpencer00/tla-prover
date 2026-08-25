---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

\* Initial state: start at 0 within the finite range
INIT == n \in NatOverride /\ n = 0

\* Step: nondeterministically advance n while staying in the range
NEXT == /\ n \in NatOverride
        /\ IF n < MaxNat THEN n' = n + 1 ELSE n' = n

\* Full specification
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

\* Predicate that a number is even (exists a natural divisor 2)
Even(m) == ∃ k \in Nat : m = 2 * k

\* Invariant stating that the double of any natural in the bounded set is even
INVARIANTS == ∀ m \in NatOverride : Even(2 * m)

\* Property to be checked (same as the invariant)
PROPERTIES == INVARIANTS
====