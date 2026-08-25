---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

\* ----------------------------------------------------------------------
\* Variables of the underlying majority‑vote algorithm.
\* They are declared here only to bind the parameters of the INSTANCE.
\* The actual definitions and evolution are given in the imported module.
\* ----------------------------------------------------------------------
VARIABLES seq, candidate, count, i

\* ----------------------------------------------------------------------
\* Import the main specification of the Boyer‑Moore majority vote algorithm.
\* It is assumed to be provided in a module named «Majority».
\* The parameters are instantiated with the identifiers used in this file.
\* ----------------------------------------------------------------------
INSTANCE Majority WITH
    Value     <- Value,
    seq       <- seq,
    candidate <- candidate,
    count     <- count,
    i         <- i

\* ----------------------------------------------------------------------
\* Specification of the whole system (as required by the .cfg file)
\* ----------------------------------------------------------------------
Spec == Majority!Spec

\* ----------------------------------------------------------------------
\* Invariants required by the .cfg file
\* ----------------------------------------------------------------------
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv     == Majority!Inv

\* ----------------------------------------------------------------------
\* Proof obligations (TLAPS will check these)
\* ----------------------------------------------------------------------
THEOREM TypeOKIsInvariant ==
  <1>1. Spec => []TypeOK
  BY TLAPS

THEOREM CorrectIsInvariant ==
  <1>1. Spec => []Correct
  BY TLAPS

THEOREM InvIsInvariant ==
  <1>1. Spec => []Inv
  BY TLAPS

====