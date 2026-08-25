---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANT Value

\* Import the main Boyer‑Moore majority vote specification.
\* It is assumed that the module `Majority` defines the core
\* variables, `Init`, `Next`, and the invariants `TypeOK`, `Correct`,
\* and `Inv`.  The local constant `Value` is supplied to the instance.
INSTANCE Majority

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Spec == Majority!Spec

\* -----------------------------------------------------------------
\* Invariants required by the configuration
\* -----------------------------------------------------------------
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv     == Majority!Inv

====