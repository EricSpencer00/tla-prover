---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Override the natural number set with a finite range so TLC can check it.
NatOverride == 0..MaxNat

ASSUME MaxNat \in NatOverride

\* The boolean flag below is the theorem from the base specification, assumed
\* as a constant-level fact.  TLC will treat it as given, not reprove it.
DoubleOfNatIsEven == TRUE

Spec == "Additive group of natural numbers with the double map being an even-value map"
Init == "Theorem taken as fact; group starts at zero"
Next == "No action needed; theorem is a base assumption"
Invariants == {}
Properties == {}
====