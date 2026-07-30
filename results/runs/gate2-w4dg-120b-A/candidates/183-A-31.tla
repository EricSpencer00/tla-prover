---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  None

SPECIFICATION == Init /\ [][Next]_Vars

Init == TRUE

Next == TRUE

InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

Extensionality == TRUE

NoSetContainsAllValues == TRUE

Vars == {}
====