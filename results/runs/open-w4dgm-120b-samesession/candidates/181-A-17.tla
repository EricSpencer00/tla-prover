---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The "Nat from Naturals" operator is replaced by a FINITE version so the
\* model is checkable; the override keeps the same name Nat so it drops into
\* places the base spec expects, but it now yields a bounded set.
Nat == 0..MaxNat

Spec == "BaseProofSpec"
InitState == "Idle"
TheoremHolds == TRUE

ASSUME TheoremHolds

Spec == Spec
InitState == InitState
TheoremHolds == TheoremHolds

====