---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, Majority

CONSTANT Value

(*--------------------------------------------------------------------
  Spec: the full behavior of the Boyer‑Moore majority vote algorithm,
  imported from the main specification module ``Majority``.
--------------------------------------------------------------------*)
Spec == Majority!Spec

(*--------------------------------------------------------------------
  Invariants required by the .cfg file.
--------------------------------------------------------------------*)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv     == Majority!Inv

=============================================================================