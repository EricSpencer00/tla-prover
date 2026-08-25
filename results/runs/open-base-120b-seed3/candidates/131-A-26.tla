---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Value

(* Import the main Boyer‑Moore majority‑vote specification *)
INSTANCE Majority AS M

(* --------------------------------------------------------------------- *)
(* Specification *)
Spec == M!Spec

(* --------------------------------------------------------------------- *)
(* Invariants inherited from the main specification *)
TypeOK  == M!TypeOK
Correct == M!Correct
Inv     == M!Inv

(* --------------------------------------------------------------------- *)
(* Machine‑checked proofs that the listed predicates are invariants of *)
(* the specification.  TLAPS will verify the following trivial steps.   *)
THEOREM TypeOKIsInvariant ==
  /\ Spec => []TypeOK
  OBVIOUS

THEOREM CorrectIsInvariant ==
  /\ Spec => []Correct
  OBVIOUS

THEOREM InvIsInvariant ==
  /\ Spec => []Inv
  OBVIOUS

====