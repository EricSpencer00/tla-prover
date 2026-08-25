---- MODULE MajorityProof ----
EXTENDS Majority, TLC

CONSTANT Value

(* No new state variables; all are inherited from Majority *)

Init == Majority!Init
Next == Majority!Next

Spec == Majority!Spec

TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

THEOREM TypeOKInvariant == Spec => []TypeOK
PROOF OBVIOUS

THEOREM CorrectInvariant == Spec => []Correct
PROOF OBVIOUS

THEOREM InvInvariant == Spec => []Inv
PROOF OBVIOUS
====