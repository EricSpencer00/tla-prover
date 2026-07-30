---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Natural numbers are overridden with a finite range for model checking.
NatOverride == 0..MaxNat

Spec0 == "Spec0"

TLCSpec == Spec0

Spec == Spec0

Init == Spec0

Next == Spec0

Invar == Spec0

Property == Spec0

====