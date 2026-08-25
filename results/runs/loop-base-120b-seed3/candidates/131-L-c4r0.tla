---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

(*-----------------------------------------------------------------
  Import the main Boyer‑Moore majority vote specification.
  It is assumed to be defined in a module named `Majority`.
-----------------------------------------------------------------*)
INSTANCE Majority AS M

(*-----------------------------------------------------------------
  Specification of the whole system.
-----------------------------------------------------------------*)
Spec == M!Spec

(*-----------------------------------------------------------------
  Invariants required by the .cfg file.
-----------------------------------------------------------------*)
TypeOK == M!TypeOK
Correct == M!Correct
Inv    == M!Inv

(*-----------------------------------------------------------------
  Proof obligations (skeletons) for TLAPS.
-----------------------------------------------------------------*)
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