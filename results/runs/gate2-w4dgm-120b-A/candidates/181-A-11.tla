---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

Spec = SumDoublesSpec

InitDoubles = SumDoublesInit

NextDoubles = SumDoublesNext

StateConstraint == SumDoublesConstraint

NatureBound == SumDoublesBound

NatOverride == 0 .. MaxNat
====