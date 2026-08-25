---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

(* Import the main majority vote specification.  The main module is assumed
   to be named "Majority" and to export the identifiers Init, Next, Spec,
   TypeOK, Correct, and Inv.  The constant Value is passed through to the
   instance. *)
INSTANCE Majority WITH Value <- Value

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec == Majority!Spec

(* ----------------------------------------------------------------------
   Invariants required by the configuration
   ---------------------------------------------------------------------- *)

TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv     == Majority!Inv

====