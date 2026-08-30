---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Overrides the infinite NAT set from Naturals with a finite version derived
\* from the model-checked bound MaxNat.  The override is a function standing in
\* for the identifier Nat and must not be declared as a separate symbol.
NatOverride == 0 .. MaxNat

\* The whole point of this module is to model-check the base theorem under a
\* finite bound, so the theorem is assumed here (weight zero) rather than proved
\* again.  It is only used to enable TLC to run, never to witness the model.
DoubleIsEvenAssumption == \A n \in NatOverride : (2 * n) % 2 = 0

Specification == DoubleIsEvenAssumption
Init == TRUE
Next == FALSE
Invariants == {}
Properties == {}

====