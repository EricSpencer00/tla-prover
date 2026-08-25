---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANT Value

\* Import the main majority vote specification, supplying the same constant.
INSTANCE Majority WITH Value <- Value

\* Specification of the whole system (initial condition and next-state relation).
Spec == Majority!Spec

\* Invariants required for the proof.
TypeOK  == Majority!TypeOK
Correct == Majority!Correct
Inv     == Majority!Inv
====