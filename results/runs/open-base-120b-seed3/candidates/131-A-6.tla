---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Value

\* Import the main Boyer‑Moore majority vote specification
INSTANCE Majority AS M

\* Specification
Spec == M!Spec

\* Invariants required by the configuration
TypeOK == M!TypeOK
Correct == M!Correct
Inv == M!Inv

====