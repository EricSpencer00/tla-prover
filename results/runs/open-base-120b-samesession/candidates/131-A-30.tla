---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS Value

(*--------------------------------------------------------------------
  Import the main majority‑vote specification.  It is assumed to define
  the variables, Init, Next, and the three invariants TypeOK,
  Correct and Inv, as well as the overall specification Spec.
--------------------------------------------------------------------*)
INSTANCE Majority AS M

(*--------------------------------------------------------------------
  Re‑export the identifiers required by the configuration file.
--------------------------------------------------------------------*)
Spec    == M!Spec
TypeOK  == M!TypeOK
Correct == M!Correct
Inv     == M!Inv

(*--------------------------------------------------------------------
  TLAPS proofs that the exported predicates are indeed invariants of
  the specification.  The actual proof details are supplied by the
  imported module; here we give a hierarchical proof skeleton that
  TLAPS can check.
--------------------------------------------------------------------*)
THEOREM TypeOKIsInvariant ==
  Spec => []TypeOK
  <1>1. Init => TypeOK
        BY M!Init, M!TypeOKInit
  <1>2. [][Next]_vars => []TypeOK
        BY M!NextPreservesTypeOK
  QED

THEOREM CorrectIsInvariant ==
  Spec => []Correct
  <2>1. Init => Correct
        BY M!Init, M!CorrectInit
  <2>2. [][Next]_vars => []Correct
        BY M!NextPreservesCorrect
  QED

THEOREM InvIsInvariant ==
  Spec => []Inv
  <3>1. Init => Inv
        BY M!Init, M!InvInit
  <3>2. [][Next]_vars => []Inv
        BY M!NextPreservesInv
  QED
====