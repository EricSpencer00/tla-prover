---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

(* Import the main majority‑vote specification. *)
INSTANCE Majority WITH Value <- Value

(* Specification of the algorithm, exported as required. *)
Spec == Majority!Spec

(* Invariants required by the configuration. *)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

====