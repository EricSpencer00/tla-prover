---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS tm, p1, p2, p3, p4, p5, p6, p7, p8

VARIABLES steps, last

vars == <<steps, last>>

TypeOK ==
  /\ steps \in Nat
  /\ last \in {p1, p2, p3, p4, p5, p6, p7, p8}

Init ==
  /\ steps = 0
  /\ last \in {p1, p2, p3, p4, p5, p6, p7, p8}

StepZenon ==
  /\ steps < tm
  /\ steps' = 1 + steps
  /\ last' = p1

StepIsabelle ==
  /\ steps < tm
  /\ steps' = 1 + steps
  /\ last' = p2

StepCVC3 ==
  /\ steps < tm
  /\ steps' = 1 + steps
  /\ last' = p3

StepYices ==
  /\ steps < tm
  /\ steps' = 1 + steps
  /\ last' = p4

StepVerit ==
  /\ steps < tm
  /\ steps' = 1 + steps
  /\ last' = p5

StepZ3 ==
  /\ steps < tm
  /\ steps' = 1 + steps
  /\ last' = p6

StepSPASS ==
  /\ steps < tm
  /\ steps' = 1 + steps
  /\ last' = p7

StepLS4 ==
  /\ steps < tm
  /\ steps' = 1 + steps
  /\ last' = p8

Next == StepZenon \/ StepIsabelle \/ StepCVC3 \/ StepYices \/ StepVerit \/ StepZ3 \/ StepSPASS \/ StepLS4

Spec == Init /\ [][Next]_vars

TheoremSetExtensionality ==
  \A A, B \in SUBSET Nat : (\A x \in A : \E y \in B : x = y) => A = B

TheoremNoUniverse ==
  \A A \in SUBSET Nat : \E x \in Nat : x \notin A

SpecOK == Spec

TheoremStepZenon == TRUE
TheoremStepIsabelle == TRUE
TheoremStepCVC3 == TRUE
TheoremStepYices == TRUE
TheoremStepVerit == TRUE
TheoremStepZ3 == TRUE
TheoremStepSPASS == TRUE
TheoremStepLS4 == TRUE

====