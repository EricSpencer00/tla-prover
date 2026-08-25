---- MODULE TLAPS ----
EXTENDS TLC

(* Backend provers *)
Zenon(p) == TRUE
Isabelle(p) == TRUE
CVC3(p) == TRUE
Yices(p) == TRUE
VeriT(p) == TRUE
Z3(p) == TRUE
SPASS(p) == TRUE
LS4(p) == TRUE

(* Temporal logic proof rules *)
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

(* Fundamental theorems *)
SetExtensionality ==
    \A A, B \in SUBSET UNIV :
        (\A x : (x \in A) <=> (x \in B)) => A = B

NoUniversalSet ==
    \A S \in SUBSET UNIV :
        \E x \in UNIV : x \notin S

(* Specification skeleton *)
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====