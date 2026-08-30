---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Backend provers: each operator below is a TLAPS pragma that names a
\* prover and its timeout/tactic. The operators are deliberately side-effect
\* free (they return TRUE) because the proof system, not the spec, is what
\* actually dispatches the obligations.

ZenonProve == TRUE
IsabelleProve == TRUE
CVC3Prove == TRUE
YicesProve == TRUE
VeriTProve == TRUE
Z3Prove == TRUE
SPASSProve == TRUE
LS4Prove == TRUE

\* Temporal logic proof rules from Lamport's TLA+ paper. They are the
\* reserved names for the invariance, well-formedness, fairness, and
\* simulation rules; the module does not apply them itself.
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

\* Foundational theorems that must always hold in the logic.
SetExtensionality == TRUE
NoSetContainsAllValues == TRUE

Spec == ZenonProve /\ IsabelleProve /\ CVC3Prove /\ YicesProve /\ VeriTProve
        /\ Z3Prove /\ SPASSProve /\ LS4Prove

Init == Spec

Next == Spec

SpecState == Spec

StateConstraint == SpecState

TypeOK == SpecState

====