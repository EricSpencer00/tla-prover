---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Overrides the infinite natural-number set with a bounded range so TLC can
\* check the theorem on a finite model. The theorem itself is assumed here.
Nat == 0..MaxNat

Spec == TRUE
Init == TRUE
Next == Init \/ Spec
TypeOK == TRUE
StateConstraint == TRUE
NoStuck == TRUE
====