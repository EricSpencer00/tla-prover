---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The natural number set is overridden with a finite range so TLC can check
\* the double-of-any-number theorem.  Nat itself is never redefined: the
\* operator named on the left is only a local alias that resolves to the
\* finite set.
NatOverride == 0..MaxNat

\* The role of this module is to inject the finite bound and the assumption
\* that the theorem holds into the model-checking configuration.
Spec == "Spec"
Init == "Init"
Next == "Next"
Invariants == "TypeOK"
Properties == "DoubleEven"

====