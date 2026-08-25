---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences
CONSTANT Value

(* Import the main Boyer‑Moore majority vote specification *)
INSTANCE Majority

(* No new state variables are introduced; we reuse those defined in Majority *)

(* ---------------------------------------------------------------------- *)
(* Specification *)
(* ---------------------------------------------------------------------- *)
Spec == Majority!Spec

(* ---------------------------------------------------------------------- *)
(* Invariants (imported from the main specification) *)
(* ---------------------------------------------------------------------- *)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv    == Majority!Inv

(* ---------------------------------------------------------------------- *)
(* TLAPS proof obligations *)
(* ---------------------------------------------------------------------- *)

THEOREM TypeOKIsInvariant ==
  Spec => []TypeOK
PROOF
  OBVIOUS
QED

THEOREM CorrectIsInvariant ==
  Spec => []Correct
PROOF
  OBVIOUS
QED

THEOREM InvIsInvariant ==
  Spec => []Inv
PROOF
  OBVIOUS
QED

====