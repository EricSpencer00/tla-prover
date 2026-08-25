---- MODULE MajorityProof ----
EXTENDS Majority

CONSTANT Value

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Majority!Spec

\* ----------------------------------------------------------------------
\* Invariants required by the configuration
\* ----------------------------------------------------------------------
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv    == Majority!Inv

\* ----------------------------------------------------------------------
\* Proof obligations (checked by TLAPS)
\* ----------------------------------------------------------------------
THEOREM TypeOKIsInvariant ==
  TypeOK
PROOF
  OBVIOUS
QED

THEOREM CorrectIsInvariant ==
  Correct
PROOF
  OBVIOUS
QED

THEOREM InvIsInvariant ==
  Inv
PROOF
  OBVIOUS
QED
====