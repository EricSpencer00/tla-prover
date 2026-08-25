---- MODULE MajorityProof ----
EXTENDS Majority, Naturals, FiniteSets, Sequences

CONSTANT Value

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec == Majority!Spec

Init == Majority!Init
Next == Majority!Next

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)

TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

====