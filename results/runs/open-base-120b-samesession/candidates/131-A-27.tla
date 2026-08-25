---- MODULE MajorityProof ----
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANT Value

(*-------------------------------------------------------------------*)
(* Import the main majority vote specification.  The main module is
   assumed to be named "Majority".  It defines the state variables,
   Init, Next, and the auxiliary predicates used below.               *)
(*-------------------------------------------------------------------*)
INSTANCE Majority WITH Value = Value

(*-------------------------------------------------------------------*)
(* Specification of the whole system.  The constant Spec is the
   formula required by the TLC configuration.                         *)
(*-------------------------------------------------------------------*)
Spec == Majority!Spec

(*-------------------------------------------------------------------*)
(* Invariants required by the configuration.  They are simply
   re‑exported from the main specification, where they are already
   defined and proved.                                                *)
(*-------------------------------------------------------------------*)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv     == Majority!Inv

(*-------------------------------------------------------------------*)
(* Optional TLAPS theorems asserting that the invariants hold for the
   whole specification.  These theorems are not required for the
   configuration but illustrate the intended proof obligations.   *)
(*-------------------------------------------------------------------*)
THEOREM TypeOKIsInvariant == Spec => []TypeOK
THEOREM CorrectIsInvariant == Spec => []Correct
THEOREM InvIsInvariant     == Spec => []Inv

====