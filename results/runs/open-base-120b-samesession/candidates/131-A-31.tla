---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences, Majority

CONSTANTS Value

(*--------------------------------------------------------------------
  Specification and invariants are taken directly from the main
  majority‑vote specification (module Majority).  The identifiers are
  aliased here so that the TLC configuration can refer to them by the
  exact names required.
--------------------------------------------------------------------*)

Spec == Majority!Spec

TypeOK == Majority!TypeOK

Inv == Majority!Inv

Correct == Majority!Correct

====