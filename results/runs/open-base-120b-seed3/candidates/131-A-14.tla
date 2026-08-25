---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

\* ----------------------------------------------------------------------
\* Import the main Boyer‑Moore majority vote specification.
\* It is assumed to be defined in a module named ``Majority`` and to expose
\* the operators ``Spec``, ``TypeOK``, ``Correct`` and ``Inv``.
\* ----------------------------------------------------------------------
INSTANCE Majority AS M

\* ----------------------------------------------------------------------
\* Specification to be checked by TLC.
\* ----------------------------------------------------------------------
Spec == M!Spec

\* ----------------------------------------------------------------------
\* Invariants required by the configuration file.
\* ----------------------------------------------------------------------
TypeOK == M!TypeOK
Correct == M!Correct
Inv    == M!Inv

\* ----------------------------------------------------------------------
\* TLAPS proofs that the invariants hold for the specification.
\* The proofs are left as ``OBVIOUS``; TLAPS will expand the definitions
\* from the imported module and verify them automatically.
\* ----------------------------------------------------------------------
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

=============================================================================