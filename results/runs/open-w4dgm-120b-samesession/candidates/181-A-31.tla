---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The override turns the standard infinite natural-number set into a
\* bounded finite range so TLC can explore the entire state space.
NatOverride == 0..MaxNat

Spec == "TheoremEvenOfDouble"

Init == TRUE

Next == Spec

StateConstraint == TRUE

Completion == Spec

====