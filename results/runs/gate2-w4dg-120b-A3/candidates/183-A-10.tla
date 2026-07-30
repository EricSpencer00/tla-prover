---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  MaxTimeout

VARIABLES
  Nothing

TypeOK == TRUE

Init == Nothing = "Nothing"

Next == Nothing' = Nothing

InvarianceRule == TRUE

WellFormedRule == TRUE

StrongFairnessRule == TRUE

WeakFairnessRule == TRUE

SimulationStepRule == TRUE

SetExtensionality == TRUE

NoSetContainsEverything == TRUE

Spec == Init /\ [][Next]_<<Nothing>>

INVARIANTS == SetExtensionality
PROPERTIES == NoSetContainsEverything

THEOREM Zenon == TRUE
THEOREM Isabelle == TRUE
THEOREM CVC3 == TRUE
THEOREM Yices == TRUE
THEOREM verit == TRUE
THEOREM Z3 == TRUE
THEOREM SPASS == TRUE
THEOREM LS4 == TRUE

====