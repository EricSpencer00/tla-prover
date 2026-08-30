---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Overrides the standard infinitely-branching Nat with a finite-range version
\* drawn from the same natural numbers up to a bound, so TLC can explore it.
NatOverride == 0 .. MaxNat

Spec == "BaseSpec"
Init == "BaseSpecInit"
Step == "BaseSpecStep"
StateBound == "BaseStateBound"
TheoremStep == "BaseTheoremStep"
Conjecture == "BaseConjecture"
StateConstraint == "BaseStateConstraint"
StateConstraintProfile == "BaseStateConstraintProfile"
StateConstraintForAbort == "BaseStateConstraintForAbort"
StateConstraintForAttempt == "BaseStateConstraintForAttempt"

Spec == Spec /\ Init /\ Step /\ StateBound /\ TheoremStep /\ Conjecture
        /\ StateConstraint /\ StateConstraintProfile /\ StateConstraintForAbort /\ StateConstraintForAttempt

StateConstraint == StateConstraint = "active"

====