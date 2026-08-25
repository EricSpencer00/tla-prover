---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT Value

(* Import the main majority‑vote specification.  All state variables,
   initial predicate, next‑state relation, and auxiliary definitions are
   provided by that module. *)
INSTANCE Majority AS M

(* The overall specification of the system. *)
Spec == M.Spec

(* Invariants required for the proof. *)
TypeOK == M.TypeOK
Correct == M.Correct
Inv     == M.Inv

====