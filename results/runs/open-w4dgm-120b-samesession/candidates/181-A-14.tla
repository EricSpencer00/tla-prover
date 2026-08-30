---- MODULE MC_sums_even ----
EXTENDS Naturals

\* Overrides the infinite natural-number set with a finite range for model
\* checking, while keeping the natural-number operations from Naturals.
NatOverride == 0..MaxNat

VARIABLES n

vars == <<n>>

TypeOK == n \in NatOverride

Init == n = 0

Next == \E m \in NatOverride : n' = m

Spec == Init /\ [][Next]_vars

\* The theorem being model-checked: the double of any natural number is even.
DoubleEven == \A x \in NatOverride : \E y \in NatOverride : 2 * x = 2 * y

\* SAFETY PROPERTY: the theorem is framed as a state invariant.
TheoremAxiom == DoubleEven

====