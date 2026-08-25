---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

(* Import the main majority vote specification. *)
INSTANCE Majority

(* Specification of the system, re‑using the definition from the main module. *)
Spec == Majority!Spec

(* Invariants imported from the main specification. *)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

====