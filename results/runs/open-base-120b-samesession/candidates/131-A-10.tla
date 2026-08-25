---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Value

(* Import the main majority vote specification *)
INSTANCE Majority WITH Value = Value

(* Specification of the system *)
Spec == Majority!Spec

(* Invariants *)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

====