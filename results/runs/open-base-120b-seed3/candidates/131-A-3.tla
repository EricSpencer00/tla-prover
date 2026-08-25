---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

\* Import the main Boyer‑Moore majority vote specification,
\* linking the constant `Value` used here to the one expected
\* by the imported module.
INSTANCE Majority WITH Value = Value

\* The overall system specification.
Spec == Majority!Spec

\* Invariants that will be proved (or assumed) for the system.
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

====