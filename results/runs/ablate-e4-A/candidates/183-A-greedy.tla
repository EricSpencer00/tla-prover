---- MODULE TLAPS ----
CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

InvarianceRule      == TRUE
WellFormednessRule  == TRUE
StrongFairnessRule  == TRUE
WeakFairnessRule    == TRUE
StepSimulationRule  == TRUE

THEOREM SetExtensionality == \A s, t \in UNIV : (s \subseteq t /\ t \subseteq s) => s = t
THEOREM NoUniversalSet   == \A s \in UNIV : s # UNIV

====