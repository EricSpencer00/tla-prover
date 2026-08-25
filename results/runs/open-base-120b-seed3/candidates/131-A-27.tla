---- MODULE MajorityProof ----
EXTENDS Majority, Naturals, Sequences, FiniteSets

CONSTANTS Value

(* Re‑export the key operators from the main majority‑vote specification *)
Spec    == Majority.Spec
TypeOK  == Majority.TypeOK
Correct == Majority.Correct
Inv     == Majority.Inv
====