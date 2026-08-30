---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* The theorem "the double of any natural number is even" is assumed at
\* the constant level for model checking across the bounded range.
ASSUME \A n \in 0..MaxNat : 2 * n \in Nat /\ (2 * n) % 2 = 0

\* NatOverride is a FINITE version of the natural numbers, shadowing the
\* infinite Nat imported from Naturals so the model stays checkable.
NatOverride == 0 .. MaxNat

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == NatOverride
PROPERTIES == TRUE

====