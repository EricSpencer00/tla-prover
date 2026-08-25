---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANT Value

(* Import the main majority vote specification. *)
INSTANCE Majority WITH Value <- Value

(* Expose the specification and invariants required by the .cfg file. *)
Spec == Majority!Spec
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv
====