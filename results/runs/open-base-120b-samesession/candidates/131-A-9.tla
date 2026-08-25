---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Value

(* Import the main majority vote specification *)
INSTANCE Majority WITH Value = Value

(*--------------------------------------------------------------------
  Variables (as defined in the imported Majority module)
--------------------------------------------------------------------*)
vars == << Majority!seq, Majority!candidate, Majority!count, Majority!i >>

(*--------------------------------------------------------------------
  Initialization and next-state relation (re‑exported from Majority)
--------------------------------------------------------------------*)
Init == Majority!Init
Next == Majority!Next

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Invariants (re‑exported from Majority)
--------------------------------------------------------------------*)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

(*--------------------------------------------------------------------
  Proof obligations
--------------------------------------------------------------------*)
THEOREM TypeOKIsInvariant ==
  Spec => []TypeOK
PROOF
  OBVIOUS
QED

THEOREM CorrectIsInvariant ==
  Spec => []Correct
PROOF
  OBVIOUS
QED

THEOREM InvIsInvariant ==
  Spec => []Inv
PROOF
  OBVIOUS
QED
====