---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Value

(*---------------------------------------------------------------------
  Import the main majority‑vote specification.  The main module is
  assumed to be named «Majority» and to define the state variables,
  the initialization predicate, the next‑state relation, and the
  invariants that we need to reuse here.
---------------------------------------------------------------------*)
INSTANCE Majority WITH Value = Value

(*---------------------------------------------------------------------
  Specification of the whole system (as required by the .cfg file).
---------------------------------------------------------------------*)
Spec == Majority!Spec

(*---------------------------------------------------------------------
  Invariants required by the .cfg file.  They are simply re‑exposed
  from the main specification so that TLAPS can refer to them under
  the names demanded by the configuration.
---------------------------------------------------------------------*)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv     == Majority!Inv

====