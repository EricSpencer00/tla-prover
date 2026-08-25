---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS Value

(* Import the main majority‑vote specification. *)
INSTANCE Majority WITH Value = Value AS M

(* The overall specification of the system. *)
Spec == M!Spec

(* Invariants required by the configuration. *)
TypeOK == M!TypeOK
Correct == M!Correct
Inv == M!Inv
====