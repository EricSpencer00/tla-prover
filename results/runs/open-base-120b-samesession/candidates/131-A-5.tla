---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

\*--------------------------------------------------------------------
\* Constants
\*--------------------------------------------------------------------
CONSTANTS Value

\*--------------------------------------------------------------------
\* Import the main majority vote specification.  It is assumed to
\* define the following operators:
\*   Init, Next, TypeOK, Correct, Inv, Spec
\*   and to use the same constant Value.
\*--------------------------------------------------------------------
INSTANCE Majority WITH Value = Value

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Majority!Spec

\*--------------------------------------------------------------------
\* Invariants
\*--------------------------------------------------------------------
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv    == Majority!Inv

\*--------------------------------------------------------------------
\* Theorem: TypeOK is an invariant of Spec
\*--------------------------------------------------------------------
THEOREM TypeOKIsInvariant ==
  ASSUME  Init == Majority!Init,
          Next == Majority!Next
  PROVE   []TypeOK
PROOF
  OBVIOUS
QED

\*--------------------------------------------------------------------
\* Theorem: Correct is an invariant of Spec
\*--------------------------------------------------------------------
THEOREM CorrectIsInvariant ==
  ASSUME  Init == Majority!Init,
          Next == Majority!Next
  PROVE   []Correct
PROOF
  OBVIOUS
QED

\*--------------------------------------------------------------------
\* Theorem: Inv (the inductive invariant from the main spec) holds
\*--------------------------------------------------------------------
THEOREM InvIsInvariant ==
  ASSUME  Init == Majority!Init,
          Next == Majority!Next
  PROVE   []Inv
PROOF
  OBVIOUS
QED

====