---- MODULE TLAPS ----

\* No constants are declared in this module.

\* Backend prover stubs. Each takes a proof obligation p and returns it unchanged.
Zenon(p) == p
Isabelle(p) == p
CVC3(p) == p
Yices(p) == p
veriT(p) == p
Z3(p) == p
SPASS(p) == p
LS4(p) == p

\* Temporal logic rule placeholders (reserved names for future use).
InvarianceRule   == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

\* Foundational theorems.
UNIV == {v | TRUE}
SetExtensionality == \A A \A B : (\A x : (x \in A \iff x \in B)) => A = B
NoUniversalSet   == \A A : ~ (A = UNIV)

\* Specification components (no state variables).
INIT          == TRUE
NEXT          == TRUE
SPECIFICATION == INIT /\ NEXT

\* Reserved invariants and properties.
INVARIANTS == SetExtensionality /\ NoUniversalSet
PROPERTIES == TRUE

====