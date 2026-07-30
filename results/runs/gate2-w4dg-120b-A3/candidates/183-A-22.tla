---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* Backend solver registration operators.  Their bodies are always TRUE because
\* they are only ever used as pragmas by the TLAPS driver, never as ordinary
\* operators in a model.
UseZenon == TRUE
UseIsabelle == TRUE
UseCVC3 == TRUE
UseYices == TRUE
UseVeriT == TRUE
UseZ3 == TRUE
UseSPASS == TRUE
UseLS4 == TRUE

Invariance == TRUE
WellFormedness == TRUE
StrongFairness == TRUE
WeakFairness == TRUE
StepSimulation == TRUE

SetExtensionality == TRUE
NoSetContainsAll == TRUE

\* The .cfg file expects a SPECIFICATION, and every module must have one.
SPECIFICATION == TRUE

\* Placeholders for the operators the .cfg mentions, even though this module
\* has no state or actions of its own.
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE
====