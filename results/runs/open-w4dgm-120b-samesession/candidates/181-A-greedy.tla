---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The finite override: Nat is redefined here as the bounded range 0..MaxNat
\* for model checking. It replaces the infinite Nat from Naturals, which is
\* why the .cfg file maps Nat to NatOverride for this module.
NatOverride == 0..MaxNat

\* The theorem from the base specification is assumed here as a constant-level
\* fact so TLC can run; the model itself has no actions to explore.
SpecAssumption == \A n \in NatOverride : (2 * n) % 2 = 0

Spec == SpecAssumption

Init == SpecAssumption

Next == SpecAssumption

StateConstraint == SpecAssumption

StateConstraint == SpecAssumption

====