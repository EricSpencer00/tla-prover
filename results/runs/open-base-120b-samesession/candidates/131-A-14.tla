---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

\* ----------------------------------------------------------------------
\* Import the core Boyer‑Moore majority vote specification.
\* It is assumed to define the state variables, Init, Next, and the
\* predicates TypeOK, Correct, Inv, as well as the overall specification
\* Spec.
\* ----------------------------------------------------------------------
INSTANCE Majority WITH Value <- Value

\* ----------------------------------------------------------------------
\* Specification and its components
\* ----------------------------------------------------------------------
Spec  == Majority!Spec
Init  == Majority!Init
Next  == Majority!Next

\* ----------------------------------------------------------------------
\* Invariants required by the configuration
\* ----------------------------------------------------------------------
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv     == Majority!Inv

\* ----------------------------------------------------------------------
\* (Optional) Theorems that TLAPS can check.  The actual proofs are
\* supplied in separate *.tla files or in the proof annotations.
\* ----------------------------------------------------------------------
\* THEOREM TypeOKIsInvariant ==
\*   Spec => []TypeOK
\*
\* THEOREM CorrectIsInvariant ==
\*   Spec => []Correct
\*
\* THEOREM InvIsInvariant ==
\*   Spec => []Inv

====