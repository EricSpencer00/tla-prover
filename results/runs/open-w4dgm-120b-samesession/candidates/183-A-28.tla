---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

Operators == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

MaxT == 1

Spec == [op : Operators, to : 0..MaxT]

SpecZ3 == [op |-> Z3, to |-> 1]

InitSpec == SpecZ3

SATimeout == [op |-> Z3, to |-> 1]

VARIABLES spec
vars == <<spec>>

SpecP == [op |-> Zenon, to |-> 0]

SpecQ == [op |-> Isabelle, to |-> 0]

Init == InitSpec

Dispatch(s) == spec' = s

DispatchZ3 == spec' = SATimeout

SpecStep == Dispatch(SpecP) \/ Dispatch(SpecQ)

SpecStepA == Dispatch(SpecP)

SpecStepB == Dispatch(SpecQ)

SpecStepC == DispatchZ3

SpecStepD == Dispatch(SATimeout)

SpecStepE == Dispatch(Spec) \/ DispatchZ3

SpecStepF == Dispatch(Spec) \/ Dispatch(SpecP)

SpecStepG == Dispatch(Spec) \/ Dispatch(SpecQ)

TLAProof == SpecStep \/ SpecStepA \/ SpecStepB \/ SpecStepC \/ SpecStepD \/ SpecStepE \/ SpecStepF \/ SpecStepG

SpecStepOp == SpecStep \/ SpecStepA \/ SpecStepB

SpecStepAlt == SpecStepC \/ SpecStepD \/ SpecStepE \/ SpecStepF \/ SpecStepG

InvarianceRule == SpecStep => (SpecStepA /\ SpecStepB)
WellFormednessRule == SpecStep => (SpecStepC /\ SpecStepD)
FairnessRule == SpecStep => SpecStepE

SETEXT ==
    \E a, b \in SUBSET Nat :
      (\A x \in Nat : (x \in a <=> x \in b)) => a = b

NOTUNIV ==
    \A b \in Nat : \E a \in SUBSET Nat : b \notin a
====