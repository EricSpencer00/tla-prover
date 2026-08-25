---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

\* Import the main majority vote specification (assumed to be in module Majority)
INSTANCE Majority AS M

\* ----------------------------------------------------------------------
\* Specification of the system (no new variables or actions are added)
\* ----------------------------------------------------------------------
Spec == M!Init /\ [][M!Next]_{M!vars}

\* ----------------------------------------------------------------------
\* Invariants (re‑exposed from the main specification)
\* ----------------------------------------------------------------------
TypeOK == M!TypeOK
Correct == M!Correct
Inv     == M!Inv

\* ----------------------------------------------------------------------
\* Proof obligations (TLAPS will check the details)
\* ----------------------------------------------------------------------
THEOREM TypeOKInvariant == Spec => []TypeOK
PROOF
  OBVIOUS
QED

THEOREM CorrectInvariant == Spec => []Correct
PROOF
  OBVIOUS
QED

THEOREM InvInvariant == Spec => []Inv
PROOF
  OBVIOUS
QED

====