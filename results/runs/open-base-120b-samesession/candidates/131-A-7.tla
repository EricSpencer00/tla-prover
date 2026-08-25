---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, Majority

CONSTANT Value

(* ----------------------------------------------------------------------
   Aliases to the definitions from the main majority‑vote specification
   (module Majority).  No new state variables or actions are introduced.
   ---------------------------------------------------------------------- *)

vars == Majority!vars

Init == Majority!Init
Next == Majority!Next

(* ----------------------------------------------------------------------
   Specification to be checked by TLC
   ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars

(* ----------------------------------------------------------------------
   Invariants required by the configuration
   ---------------------------------------------------------------------- *)

TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

====