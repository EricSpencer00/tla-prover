---- MODULE MC_sums_even ----
EXTENDS Integers, Naturals

CONSTANTS MaxNat

SPECIFICATION == "FinitenessCheck"
INIT == "FinitenessCheck"
NEXT == "FinitenessCheck"
INVARIANTS == "FinitenessCheck"
PROPERTIES == "FinitenessCheck"

NatOverride == Nat \ {MaxNat}
====