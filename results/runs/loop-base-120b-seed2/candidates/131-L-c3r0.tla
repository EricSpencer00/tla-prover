---- MODULE MajorityProof ----
EXTENDS Majority

CONSTANT Value

(*-----------------------------------------------------------------
  Specification (imported from the main majority vote module)
-----------------------------------------------------------------*)
Spec == Majority!Spec

(*-----------------------------------------------------------------
  Invariants (imported from the main majority vote module)
-----------------------------------------------------------------*)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

(*-----------------------------------------------------------------
  Theorems stating that the invariants hold for Spec
-----------------------------------------------------------------*)
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