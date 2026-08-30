---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* This operator replaces the infinite Nat set from Naturals with a bounded
\* version so TLC can check the model; the override skips the declaration.
NatOverride == 0 .. MaxNat

SPECIFICATION == 1
INIT == 1
NEXT == 1
INVARIANTS == 1
PROPERTIES == 1

====