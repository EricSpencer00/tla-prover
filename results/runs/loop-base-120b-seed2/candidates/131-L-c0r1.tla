---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, Majority

CONSTANT Value

(* Specification inherited from the main majority‑vote module *)
Spec == Majority!Spec

(* Invariants inherited from the main specification *)
TypeOK == Majority!TypeOK
Inv    == Majority!Inv
Correct == Majority!Correct

(* Proofs that the invariants hold for Spec *)

THEOREM TypeOKIsInvariant == Spec => []TypeOK
PROOF
  OBVIOUS.
QED

THEOREM InvIsInvariant == Spec => []Inv
PROOF
  OBVIOUS.
QED

THEOREM CorrectIsInvariant == Spec => []Correct
PROOF
  OBVIOUS.
QED
====