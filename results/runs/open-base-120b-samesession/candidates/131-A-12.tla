---- MODULE MajorityProof ----
EXTENDS Majority, TLC, FiniteSets, Sequences

CONSTANT Value

(*-----------------------------------------------------------------
   Specification of the algorithm (imported from the main module)
 -----------------------------------------------------------------*)
Spec == Majority!Spec

(*-----------------------------------------------------------------
   Invariants imported from the main specification
 -----------------------------------------------------------------*)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv     == Majority!Inv

(*-----------------------------------------------------------------
   TLAPS proofs that the invariants hold for Spec
 -----------------------------------------------------------------*)
THEOREM TypeOKIsInvariant == Spec => []TypeOK
PROOF OBVIOUS

THEOREM CorrectIsInvariant == Spec => []Correct
PROOF OBVIOUS

THEOREM InvIsInvariant == Spec => []Inv
PROOF OBVIOUS

====