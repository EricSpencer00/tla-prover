---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, Majority

CONSTANT Value

(*--------------------------------------------------------------------
  Aliases to the definitions from the main majority‑vote specification.
  The main specification (module Majority) defines the state variables,
  the initial predicate, the next‑state relation, the overall
  specification, and the key invariants.
--------------------------------------------------------------------*)

Init  == Majority!Init
Next  == Majority!Next
Spec  == Majority!Spec

(*--------------------------------------------------------------------
  Invariants required by the TLC configuration.
--------------------------------------------------------------------*)

TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv     == Majority!Inv

=============================================================================