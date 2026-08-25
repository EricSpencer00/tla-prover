---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Value

(* Import the main majority‑vote specification.  It is assumed to define
   the variables, Init, Next, Spec, and the invariants TypeOK, Correct,
   and Inv.  The constant Value is passed through to the instance. *)
INSTANCE Majority WITH Value <- Value

(* The top‑level specification of the system. *)
Spec == Majority!Spec

(* Invariants required by the configuration file. *)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv
====