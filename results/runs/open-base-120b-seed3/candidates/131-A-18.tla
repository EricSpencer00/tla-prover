---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences
CONSTANT Value

\* Import the main majority vote specification, binding the constant Value.
INSTANCE Majority WITH Value <- Value

\* Specification (inherits the whole behavior from the main spec)
Spec == Majority!Spec

\* Invariants required by the proof
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv
====