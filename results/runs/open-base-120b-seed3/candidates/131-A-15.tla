---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

\* Import the main majority vote specification
INSTANCE Majority

\* Specification of the whole system
Spec == Majority!Spec

\* Invariants imported from the main specification
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

\* Theorem: type correctness is an invariant
THEOREM TypeOKIsInvariant ==
  Spec => []TypeOK
PROOF
  OBVIOUS
QED

\* Theorem: algorithm correctness is an invariant
THEOREM CorrectIsInvariant ==
  Spec => []Correct
PROOF
  OBVIOUS
QED

\* Theorem: auxiliary invariant holds throughout execution
THEOREM InvIsInvariant ==
  Spec => []Inv
PROOF
  OBVIOUS
QED
====