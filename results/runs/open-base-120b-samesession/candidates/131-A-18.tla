---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets
CONSTANTS Value

(* Import the main majority vote specification and bind the constant Value *)
INSTANCE Majority WITH Value <- Value

(* Specification of the whole system *)
Spec == Majority!Spec

(* Invariants imported from the main specification *)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

(* Proof obligations for TLAPS *)

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