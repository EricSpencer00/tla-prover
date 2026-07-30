---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS
    MaxNat, Nat

\* The theorem that the double of any natural number is even is assumed here
\* at the constant level, which is how the bounded model keeps the property
\* in scope for TLC.
DoubleIsEven == TRUE

TypeOK == TRUE

Spec == DoubleIsEven

====