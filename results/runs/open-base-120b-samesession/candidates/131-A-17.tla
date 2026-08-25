---- MODULE MajorityProof ----
EXTENDS Majority, TLC

CONSTANTS Value

(*--------------------------------------------------------------------
  The main majority vote algorithm specification is defined in the
  module `Majority`.  This proof module re‑exports the relevant
  definitions so that the TLAPS configuration can refer to them.
--------------------------------------------------------------------*)

Spec == Majority!Spec

TypeOK == Majority!TypeOK

Correct == Majority!Correct

Inv == Majority!Inv

====