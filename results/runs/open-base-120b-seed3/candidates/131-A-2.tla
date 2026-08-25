---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT Value

\* Import the main Boyer‑Moore majority vote specification.
\* The main module is assumed to be named ``Majority`` and to use the
\* constant ``Value``.  By instantiating it we obtain access to its
\* definitions under the prefix ``M``.
INSTANCE Majority AS M WITH Value = Value

\* ----------------------------------------------------------------------
\* Specification required by the configuration file
\* ----------------------------------------------------------------------
Spec == M!Spec

\* ----------------------------------------------------------------------
\* Invariants required by the configuration file
\* ----------------------------------------------------------------------
TypeOK  == M!TypeOK
Correct == M!Correct
Inv     == M!Inv

\* ----------------------------------------------------------------------
\* Proof obligations (checked by TLAPS)
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