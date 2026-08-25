---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT Value

(* Import the main majority‑vote specification. All state variables,
   initial predicate, next‑state relation, and auxiliary definitions are
   provided by that module. *)
INSTANCE Majority

(* The overall specification of the system. *)
Spec == Majority!Spec

(* Invariants required for the proof. *)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv    == Majority!Inv
====