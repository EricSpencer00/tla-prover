---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

(* Import the main majority‑vote specification. *)
INSTANCE Majority

(* Specification and invariants are taken directly from the imported module. *)
Spec == Majority!Spec
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

====