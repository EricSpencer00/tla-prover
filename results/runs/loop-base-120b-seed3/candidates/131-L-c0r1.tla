---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value, cand, seq, cnt, i

(* Import the main majority vote specification, providing substitutions for its parameters. *)
INSTANCE Majority AS M WITH cand = cand, seq = seq, cnt = cnt, i = i

(* Specification of the system, re‑using the definition from the main module. *)
Spec == M!Spec

(* Invariants imported from the main specification. *)
TypeOK == M!TypeOK
Correct == M!Correct
Inv == M!Inv
====