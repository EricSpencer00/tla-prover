---- MODULE MajorityProof ----
CONSTANT Value

EXTENDS Naturals, Sequences, FiniteSets

INSTANCE Majority WITH Value <- Value

(* The overall specification of the system *)
Spec == Majority!Spec

(* Invariants inherited from the main specification *)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

(* Proof that the type-correctness invariant holds *)
THEOREM TypeOKIsInvariant ==
  Spec => []TypeOK
PROOF
  OBVIOUS
QED

(* Proof that the correctness invariant holds *)
THEOREM CorrectIsInvariant ==
  Spec => []Correct
PROOF
  OBVIOUS
QED

(* Proof that the auxiliary invariant holds *)
THEOREM InvIsInvariant ==
  Spec => []Inv
PROOF
  OBVIOUS
QED

====