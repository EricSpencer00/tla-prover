---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

\* Import the main majority‑vote specification
INSTANCE Majority

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Invariants required by the configuration
\* ----------------------------------------------------------------------
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv     == Majority!Inv

=============================================================================