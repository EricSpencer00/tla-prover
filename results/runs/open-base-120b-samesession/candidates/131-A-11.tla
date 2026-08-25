---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

\* ----------------------------------------------------------------------
\* Import the main Boyer‑Moore majority vote specification.
\* It is assumed to be provided in a module named «Majority».
\* ----------------------------------------------------------------------
INSTANCE Majority

\* The complete specification (initial condition and next‑state relation)
Spec == Majority!Spec

\* Invariant stating that all variables have values of the intended types.
TypeOK == Majority!TypeOK

\* Invariant stating the algorithm’s functional correctness:
\* any element appearing in a strict majority of the input sequence
\* must equal the final candidate.
Correct == Majority!Correct

\* The inductive invariant used in the main specification.
Inv == Majority!Inv

====