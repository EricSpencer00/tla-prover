---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

VARIABLES cand, seq, cnt, i

\* Import the main majority‑vote specification, providing substitutions for its
\* state variables.
INSTANCE Majority WITH cand <- cand, seq <- seq, cnt <- cnt, i <- i

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Init == Majority!Init
Next == Majority!Next
Vars == Majority!Vars

Spec == Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Invariants required by the configuration
\* ----------------------------------------------------------------------
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv     == Majority!Inv

=============================================================================