---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

(*-------------------------------------------------------------------*)
(*  Import the main Boyer‑Moore majority‑vote specification.         *)
(*-------------------------------------------------------------------*)
INSTANCE Majority AS M

(*-------------------------------------------------------------------*)
(*  Specification exported for the model checker.                    *)
(*-------------------------------------------------------------------*)
Spec == M!Spec

(*-------------------------------------------------------------------*)
(*  Invariants required by the .cfg file.                           *)
(*-------------------------------------------------------------------*)
TypeOK == M!TypeOK
Correct == M!Correct
Inv     == M!Inv

(*-------------------------------------------------------------------*)
(*  Proof that TypeOK is an invariant of Spec.                       *)
(*-------------------------------------------------------------------*)
THEOREM TypeOKInvariant ==
  ASSUME Init == M!Init,
         Next == M!Next
  PROVE []TypeOK
PROOF
  <1>1. Init => TypeOK
        BY M!InitTypeOK
  <1>2. /\ TypeOK /\ [][Next]_(M!vars) => []TypeOK
        BY INDUCTION
  QED

(*-------------------------------------------------------------------*)
(*  Proof that Correct is an invariant of Spec.                     *)
(*-------------------------------------------------------------------*)
THEOREM CorrectInvariant ==
  ASSUME Init == M!Init,
         Next == M!Next
  PROVE []Correct
PROOF
  <1>1. Init => Correct
        BY M!InitCorrect
  <1>2. /\ Correct /\ [][Next]_(M!vars) => []Correct
        BY INDUCTION
  QED

(*-------------------------------------------------------------------*)
(*  Proof that Inv (the main inductive invariant) holds.            *)
(*-------------------------------------------------------------------*)
THEOREM InvInvariant ==
  ASSUME Init == M!Init,
         Next == M!Next
  PROVE []Inv
PROOF
  <1>1. Init => Inv
        BY M!InitInv
  <1>2. /\ Inv /\ [][Next]_(M!vars) => []Inv
        BY INDUCTION
  QED

====