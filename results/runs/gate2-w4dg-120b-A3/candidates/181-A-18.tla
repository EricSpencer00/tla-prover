---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* This module is a model-checking configuration for the proof that the double
\* of any natural number is even.  It inherits the base proof's definitions and
\* overrides the natural number set with a finite range so TLC can check it.

\* The .cfg file overrides the infinite Nat with a finite version here.  The
\* name "Nat" is never declared or redefined; the operator on the right is the
\* bounded version that replaces the inherited one.
NatOverride == 0..MaxNat

\* The overall specification is the single-step proof from the base spec.
SPECIFICATION == ProofStep

\* The base proof has a single initial state, so INIT refers to that inherited
\* definition unchanged.
INIT == InitState

\* The proof's step is the only transition, so NEXT closes on that one action.
NEXT == NextStep

\* The theorem is taken as an assumption for model checking and is what the
\* check is run against.
INVARIANTS == DoubleEven

\* A correctly bound model has no outstanding liveness requirements.
PROPERTIES == {}
====