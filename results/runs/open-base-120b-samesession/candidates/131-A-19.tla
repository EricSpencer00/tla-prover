---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

(* Import the main majority vote specification, tying the constant Value *)
INSTANCE Majority WITH Value = Value

(* Specification to be checked *)
Spec == Majority!Spec

(* Invariants required by the proof *)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

====