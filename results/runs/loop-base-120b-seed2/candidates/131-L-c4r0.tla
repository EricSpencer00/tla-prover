---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

(* Import the main majority‑vote specification. *)
INSTANCE Majority AS Maj WITH Value <- Value

(* Specification of the algorithm, exported as required. *)
Spec == Maj!Spec

(* Invariants required by the configuration. *)
TypeOK == Maj!TypeOK
Correct == Maj!Correct
Inv == Maj!Inv

====