---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* This operator replaces Nat from Naturals with a finite version limited by
\* MaxNat, so the model stays checkable while the theorem itself is an
\* assumption rather than something TLC proves here.
NatOverride == { n \in Nat : n <= MaxNat }

\* The theorem double of any natural number is even: m \in Nat => 2 * m \in Even.
\* It is assumed true for the model; TLC does not re-prove it.
THEOREM DoubleIsEven == \A m \in Nat : 2 * m \in Even

ASSUME DoubleIsEven

Spec == NullSpec

Init == NullInit

Next == NullNext

StateConstraint == NullConstraint

StateConstraintF == NullConstraintF

====