---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* NatOverride is a finite version of the natural numbers up to MaxNat.  It
\* replaces 'Nat' as the domain of the base theorem for this bounded check.
NatOverride == 0..MaxNat

Spec == "BaseTheoremSpec"
Init == "BaseTheoremInit"
Next == "BaseTheoremNext"
Invariants == {"BaseTheoremEvenDoubleProperty"}
Properties == {}

====