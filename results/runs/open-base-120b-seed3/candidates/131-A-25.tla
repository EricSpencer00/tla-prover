---- MODULE MajorityProof ----
EXTENDS TLC, Majority

CONSTANT Value

(*-----------------------------------------------------------------
   State variables (same as in Majority module)
-----------------------------------------------------------------*)
VARIABLES candidate, count, i, seq

(*-----------------------------------------------------------------
   Helper definition for the set of all variables
-----------------------------------------------------------------*)
vars == <<candidate, count, i, seq>>

(*-----------------------------------------------------------------
   Initialization and next-state relation are taken from the
   main specification.
-----------------------------------------------------------------*)
Init == Majority!Init
Next == Majority!Next

(*-----------------------------------------------------------------
   Specification of the system
-----------------------------------------------------------------*)
Spec == Init /\ [] [Next]_vars

(*-----------------------------------------------------------------
   Invariants imported from the main specification
-----------------------------------------------------------------*)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

=============================================================================