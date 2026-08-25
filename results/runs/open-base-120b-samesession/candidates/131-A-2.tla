---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANT Value

\* ----------------------------------------------------------------------
\* Import the main Boyer‑Moore majority vote specification.
\* The main module (named Majority) is assumed to define the algorithm
\* variables, Init, Next, Spec, and the invariants TypeOK, Correct, Inv.
\* We instantiate it, supplying the constant Value required by that module.
\* ----------------------------------------------------------------------
INSTANCE Majority AS M WITH Value <- Value

\* ----------------------------------------------------------------------
\* The overall specification of the system.
\* ----------------------------------------------------------------------
Spec == M!Spec

\* ----------------------------------------------------------------------
\* Invariants required by the TLC configuration.
\* ----------------------------------------------------------------------
TypeOK == M!TypeOK
Correct == M!Correct
Inv    == M!Inv

\* ----------------------------------------------------------------------
\* TLAPS proof skeletons (machine‑checked proofs can be filled in later).
\* ----------------------------------------------------------------------
THEOREM TypeOKIsInvariant == Spec => []TypeOK
PROOF
  OBVIOUS
QED

THEOREM CorrectIsInvariant == Spec => []Correct
PROOF
  OBVIOUS
QED

THEOREM InvIsInvariant == Spec => []Inv
PROOF
  OBVIOUS
QED

====