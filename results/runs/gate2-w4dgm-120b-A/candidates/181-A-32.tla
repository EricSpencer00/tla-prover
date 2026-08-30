---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The model-checking configuration for the "double is even" theorem.
\* It inherits the core definitions from the base proof spec and
\* overrides the natural number set to a finite range so TLC can check.
\* MaxNat (one million) is a constant, with no distinct runtime range.

VARIABLES n
vars == << n >>

Init == n = 0

Next == /\ n < MaxNat
        /\ n' = n + 1

Spec == Init /\ [][Next]_vars

\* Theorem (assumed here as a constant-level fact for TLC): the double
\* of any natural number is even. It is assumed true for the check.
DoubleEven == \A m \in 1..MaxNat : (2 * m) % 2 = 0

StateConstraint == n <= MaxNat

SpecConstrained == Spec /\ StateConstraint

====