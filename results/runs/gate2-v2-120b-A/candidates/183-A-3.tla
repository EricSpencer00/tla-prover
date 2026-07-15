---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(* ----------------------------------------------------------------------
   This module defines the backend pragmas for TLAPS and states the two
   foundational theorems required by the description.
   No state variables or actions are needed because the module only
   provides configuration operators and theorems.
   ---------------------------------------------------------------------- *)

\* ----------------------------------------------------------------------
   Backend pragmas (operators) – their bodies are empty because the
   actual implementation is provided by the TLAPS tool.
   The names are reserved and can be used in proofs.
   ---------------------------------------------------------------------- *)

Zenon(assrt) == assrt
Isabelle(assrt) == assrt
CVC3(assrt) == assrt
Yices(assrt) == assrt
VeriT(assrt) == assrt
Z3(assrt) == assrt
SPASS(assrt) == assrt
LS4(assrt) == assrt

\* ----------------------------------------------------------------------
   Temporal logic proof rule names – also empty definitions, serving only
   as reserved identifiers.
   ---------------------------------------------------------------------- *)

InvariantRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE
ExtensibilityRule == TRUE
NoUniversalSetRule == TRUE

\* ----------------------------------------------------------------------
   Foundational theorems
   ---------------------------------------------------------------------- *)

SetExtensionality ==
    \A X, Y \in SUBSET S :
        (\A a : a \in X <=> a \in Y) => X = Y

NoUniversalSet ==
    \A Y \in SUBSET S : ~(\A a \in S : a \in Y)

\* ----------------------------------------------------------------------
   Constants
   ---------------------------------------------------------------------- *)

CONSTANT S

\* ----------------------------------------------------------------------
   Specification operators required by the generic .cfg file.
   The system has no state, so the spec is trivially true.
   ---------------------------------------------------------------------- *)

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

\* ----------------------------------------------------------------------
   THEOREM declarations to make TLC check the two foundational theorems.
   ---------------------------------------------------------------------- *)

THEOREM SetExtensionalityTheorem == SetExtensionality
THEOREM NoUniversalSetTheorem == NoUniversalSet

====