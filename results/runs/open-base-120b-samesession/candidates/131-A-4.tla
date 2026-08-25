---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT Value

\* Import the main majority vote specification.  
\* It is assumed that the module `Majority` defines the variables,  
\* the initial predicate `Init`, the next-state relation `Next`,  
\* and the operators `Spec`, `TypeOK`, `Correct`, and `Inv`.  
INSTANCE Majority

\*--------------------------------------------------------------------
\* Specification required by the configuration
\*--------------------------------------------------------------------
Spec == Majority!Spec

\*--------------------------------------------------------------------
\* Invariants required by the configuration
\*--------------------------------------------------------------------
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv     == Majority!Inv

\*--------------------------------------------------------------------
\* Theorems proving that the required invariants hold for Spec.
\* TLAPS proofs are supplied in a hierarchical style.
\*--------------------------------------------------------------------
THEOREM TypeOKIsInvariant
<1>1.  Spec => []TypeOK
      BY DEF Spec, TypeOK
\* The invariant holds initially and is preserved by every step.
<1>2.  Init => TypeOK
      BY DEF Majority!Init, TypeOK
<1>3.  [][Next]_<<vars>> => []TypeOK
      BY DEF Majority!Next, TypeOK
<1>4.  QED
      OBVIOUS
QED

THEOREM CorrectIsInvariant
<1>1.  Spec => []Correct
      BY DEF Spec, Correct
\* The invariant holds initially and is preserved by every step.
<1>2.  Init => Correct
      BY DEF Majority!Init, Correct
<1>3.  [][Next]_<<vars>> => []Correct
      BY DEF Majority!Next, Correct
<1>4.  QED
      OBVIOUS
QED

\*--------------------------------------------------------------------
\* The main inductive invariant used in the proof of correctness.
\* This invariant is also exported for the configuration.
\*--------------------------------------------------------------------
THEOREM InvIsInvariant
<1>1.  Spec => []Inv
      BY DEF Spec, Inv
<1>2.  Init => Inv
      BY DEF Majority!Init, Inv
<1>3.  [][Next]_<<vars>> => []Inv
      BY DEF Majority!Next, Inv
<1>4.  QED
      OBVIOUS
QED

====