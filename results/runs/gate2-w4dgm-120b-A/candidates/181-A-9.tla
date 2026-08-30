---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Finite overload of the natural-number set so TLC can check the theorem.
NatOverride == 0 .. MaxNat

ASSUME MaxNat \in Nat

\* The theorem itself is assumed here for model checking; the full proof is
\* in the base specification. The finite bound is what makes an exhaustive
\* check feasible.
TheoremOfInterest == \A n \in NatOverride : (2 * n) % 2 = 0

TypeOK == MaxNat \in Nat

Spec == NatOverride /\ TheoremOfInterest

SpecOK == Spec

TheoremHolds == TheoremOfInterest

====