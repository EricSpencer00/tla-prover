---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS Zenon, Isabelle, CVC3, Yices, Verit, Z3, SPASS, LS4, NoTimeout

ASSUME /\ Zenon \in Nat /\ Isabelle \in Nat /\ CVC3 \in Nat
       /\ Yices \in Nat /\ Verit \in Nat /\ Z3 \in Nat
       /\ SPASS \in Nat /\ LS4 \in Nat

DispatchToZenon == Zenon
DispatchToIsabelle == Isabelle
DispatchToCVC3 == CVC3
DispatchToYices == Yices
DispatchToVerit == Verit
DispatchToZ3 == Z3
DispatchToSPASS == SPASS
DispatchToLS4 == LS4

NoTimeoutDispatched == NoTimeout

EXTENDS Temporal

Spec == TRUE
Init == TRUE
Next == TRUE
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
SimulationStepRule == TRUE

SetExtensionality ==
  \A A \in SUBSET Nat, B \in SUBSET Nat :
     (\A x \in Nat : (x \in A) <=> (x \in B)) => A = B

NoSetContainsAllNumbers ==
  \A A \in SUBSET Nat : (\A x \in Nat : x \in A) => FALSE

====