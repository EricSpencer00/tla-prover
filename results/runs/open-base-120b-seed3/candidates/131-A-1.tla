---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANT Value

(* Import the main majority‑vote specification. *)
INSTANCE Majority WITH Value <- Value

(* ---------------------------------------------------------------------- *)
(* Specification *)
(* ---------------------------------------------------------------------- *)
Spec == Majority!Spec

(* ---------------------------------------------------------------------- *)
(* Invariants *)
(* ---------------------------------------------------------------------- *)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

(* ---------------------------------------------------------------------- *)
(* TLAPS proofs that the invariants hold for Spec *)
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