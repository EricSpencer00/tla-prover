---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Value

(* Import the main majority‑vote algorithm specification.
   The main module is assumed to be named ``Majority`` and to use the
   same constant ``Value``. *)
INSTANCE Majority WITH Value = Value AS M

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == M!Spec

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)
TypeOK == M!TypeOK
Correct == M!Correct
Inv == M!Inv

====