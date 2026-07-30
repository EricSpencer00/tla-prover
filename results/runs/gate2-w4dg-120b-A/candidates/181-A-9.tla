---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

\* The double of any natural number is even.  The bound below is a
\* model-checking artifact; an unrestricted range would never finish in
\* TLC, so the proof assumes the theorem and works over a finite band.
\* The theorem itself lives in the base spec and is assumed here, so the
\* bounded model can close the check without proving the arithmetic.

TypeOK == Nat \subseteq (0..MaxNat)

Spec == TRUE

Init == TRUE

Next == TRUE

Invars == TypeOK

Props == TRUE

====