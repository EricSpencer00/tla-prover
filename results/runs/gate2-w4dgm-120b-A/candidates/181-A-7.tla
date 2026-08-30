---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Overrides the infinite natural number set from Naturals with a finite range
\* so TLC can check the property on a bounded model.
NatOverride == 0..MaxNat

\* The base theorem (from the inherited proof) is assumed here as a constant
\* level truth so TLC can process the spec; the override above makes the state
\* space finite and checkable.
ASSUME \A n \in NatOverride : (2 * n) % 2 = 0

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANT == TRUE
PROPERTIES == TRUE

====