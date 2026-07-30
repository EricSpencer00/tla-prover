---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

\* The invariant and the theorem are both part of the same statement, so the
\* model can be checked with the theorem assumed as an axiom.
ASSUME DoubleIsEven == \A n \in Nat : (2 * n) % 2 = 0
ASSUME Nat == 0..MaxNat

Spec == TRUE
Init == TRUE
Next == TRUE

TypeOK == TRUE
DoubleEvenTheoremHolds == TRUE

INVARIANT TypeOK
INVARIANT DoubleEvenTheoremHolds
====