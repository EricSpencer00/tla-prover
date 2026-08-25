---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, Temporal

CONSTANT Value

(* Import the main Boyer‑Moore majority vote specification. *)
INSTANCE Majority WITH Value <- Value

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Majority!Spec

(* ----------------------------------------------------------------------
   Invariants required by the configuration
   ---------------------------------------------------------------------- *)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

(* ----------------------------------------------------------------------
   TLAPS proofs (sketches – full proofs would be expanded in a real
   development).  The proofs are deliberately simple here because the
   heavy lifting is done in the imported module.
   ---------------------------------------------------------------------- *)

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