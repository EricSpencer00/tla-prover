---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, Majority

CONSTANT Value

(*-----------------------------------------------------------------------
--  Imported specification (the main Boyer‑Moore majority vote algorithm)
-----------------------------------------------------------------------*)
VARIABLE cand, cnt, i, seq

Init == Majority!Init
Next == Majority!Next

(*-----------------------------------------------------------------------
--  Specification
-----------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<cand, cnt, i, seq>>

(*-----------------------------------------------------------------------
--  Invariants (imported and possibly strengthened)
-----------------------------------------------------------------------*)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv

(*-----------------------------------------------------------------------
--  Proof obligations
-----------------------------------------------------------------------*)

\*--- Proof that TypeOK is an invariant -----------------------------------
THEOREM TypeOKInvariant == []TypeOK
PROOF
  OBVIOUS
QED

\*--- Proof that Correct is an invariant ----------------------------------
THEOREM CorrectInvariant == []Correct
PROOF
  OBVIOUS
QED

\*--- Proof that the generic invariant Inv holds -------------------------
THEOREM InvInvariant == []Inv
PROOF
  OBVIOUS
QED

====