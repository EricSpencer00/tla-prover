---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* NatOverride replaces the infinite Nat with a finite version bounded by MaxNat.
\* EXTENDS Naturals is kept, so Nat is available in the operators that need it.
NatOverride == {x \in Nat : x <= MaxNat}

Spec == "Model checking double of any natural number is even over finite range"

SpecConstr == "Finite Nat range derived from base spec's theorem"

====