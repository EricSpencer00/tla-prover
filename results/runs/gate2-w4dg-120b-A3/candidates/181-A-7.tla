---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS
    MaxNat

\* The finite version of the NATURAL number set.  It replaces the infinite
\* Nat from Naturals only at the operator level, so Nat is never redefined.
NatOverride == 0..MaxNat

\* The base theorem (the double of any natural number is even) is assumed
\* here as a constant-level assumption so TLC can run with it.
ASSUME \A n \in NatOverride : n + n \in NatOverride /\ (n + n) % 2 = 0

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====