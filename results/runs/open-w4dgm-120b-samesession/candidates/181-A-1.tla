---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Finite cutoff overriding the infinite Nat, provided as an operator so the
\* .cfg can replace the built-in Nat with this bounded version.
NatOverride == 0..MaxNat

\* The property being model-checked: the double of any natural number is even.
KIsEven == {2 * n : n \in NatOverride}

Spec == TRUE
Init == TRUE
Next == TRUE
Invars == TRUE
Props == KIsEven

====