---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Value

(* Import the main Boyer‑Moore majority vote specification *)
INSTANCE Majority WITH Value <- Value

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec == Majority!Spec

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)

(* Type correctness invariant, as defined in the main specification *)
TypeOK == Majority!TypeOK

(* Main correctness invariant, as defined in the main specification *)
Correct == Majority!Correct

(* Combined invariant used in the proof *)
Inv == TypeOK /\ Correct

(* ----------------------------------------------------------------------
   Proof obligations
   ---------------------------------------------------------------------- *)

THEOREM TypeOKInvariant == Spec => []TypeOK
PROOF
  BY INSTANCE Majority!TypeOKInvariant
QED

THEOREM CorrectInvariant == Spec => []Correct
PROOF
  BY INSTANCE Majority!CorrectInvariant
QED

THEOREM InvInvariant == Spec => []Inv
PROOF
  BY TypeOKInvariant, CorrectInvariant
QED

====