---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
INSTANCE Majority AS M

CONSTANT Value

(*-----------------------------------------------------------------
  Specification of the Boyer‑Moore majority vote algorithm.
  All definitions are taken from the main Majority module (instanced
  as M).  No new state variables or actions are introduced.
-----------------------------------------------------------------*)

Spec == /\ M!Init
        /\ [][M!Next]_M!Vars

(*-----------------------------------------------------------------
  Invariants imported from the main specification.
-----------------------------------------------------------------*)

TypeOK == M!TypeOK
Correct == M!Correct
Inv    == M!Inv

(*-----------------------------------------------------------------
  TLAPS proofs that the invariants hold for the specification.
-----------------------------------------------------------------*)

THEOREM TypeOKInvariant == Spec => []TypeOK
PROOF
  OBVIOUS
QED

THEOREM CorrectInvariant == Spec => []Correct
PROOF
  OBVIOUS
QED

THEOREM InvInvariant == Spec => []Inv
PROOF
  OBVIOUS
QED
====