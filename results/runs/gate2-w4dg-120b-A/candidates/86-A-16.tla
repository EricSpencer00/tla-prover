---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  ZENO, ISABELLE, CVC3, YICES, VERIT, Z3, SPASS, LS4

VARIABLES
  used

vars == << used >>

Used == {ZENO, ISABELLE, CVC3, YICES, VERIT, Z3, SPASS}

TypeOK == used \subseteq Used

Init == used = Used

Refresh == used = Used /\ UNCHANGED vars

Spec ==
  /\ Init
  /\ Refresh

Zenon == ZENO
Isabelle == ISABELLE
Cvc3 == CVC3
Yices == YICES
Verit == VERIT
ZThree == Z3
Spass == SPASS
Temporal == LS4

SetExtensionality == \A S, T \in SUBSET Nat : (\A x \in Nat : (x \in S) <=> (x \in T)) => (S = T)
NoUniversalSet == ~(\E S \in SUBSET Nat : \A x \in Nat : x \in S)

InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
SimulationStepRule == TRUE

====