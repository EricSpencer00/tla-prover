---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Value

(* Import the main Boyer‑Moore majority vote specification, 
   passing the required constant. *)
INSTANCE Majority WITH Value <- Value

(* The overall specification of the system. *)
Spec == Majority!Spec

(* Invariant asserting that all state variables have the correct types. *)
TypeOK == Majority!TypeOK

(* Invariant asserting the correctness of the algorithm's output. *)
Correct == Majority!Correct

(* The inductive invariant used in the main specification. *)
Inv == Majority!Inv

====