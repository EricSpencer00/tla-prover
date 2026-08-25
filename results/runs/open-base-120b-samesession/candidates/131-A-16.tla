---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences, Majority

CONSTANTS Value

(*--------------------------------------------------------------------*)
(*  Specification                                                    *)
(*--------------------------------------------------------------------*)
Spec == Majority!Spec

(*--------------------------------------------------------------------*)
(*  Invariants                                                       *)
(*--------------------------------------------------------------------*)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

(*--------------------------------------------------------------------*)
(*  Proof obligations (place‑holders for TLAPS)                      *)
(*--------------------------------------------------------------------*)
THEOREM TypeOKInvariant == Spec => []TypeOK
THEOREM CorrectInvariant == Spec => []Correct

====