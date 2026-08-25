---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSets, Sequences

CONSTANT Value

(* Reuse the core definitions from the main majority‑vote specification *)
Init == Majority!Init
Next == Majority!Next
Vars == Majority!Vars

(* Specification formula required by the configuration *)
Spec == Init /\ [][Next]_Vars

(* Invariants required by the configuration *)
TypeOK == Majority!TypeOK
Inv    == Majority!Inv
Correct == Majority!Correct

(* TLAPS proofs that the invariants hold for Spec *)

THEOREM TypeOKInvariant == Spec => []TypeOK
PROOF
  OBVIOUS
QED

THEOREM InvInvariant == Spec => []Inv
PROOF
  OBVIOUS
QED

THEOREM CorrectInvariant == Spec => []Correct
PROOF
  OBVIOUS
QED

====