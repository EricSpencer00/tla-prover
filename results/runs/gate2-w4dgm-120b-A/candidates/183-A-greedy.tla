---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Backend provers: each operator below is a TLAPS pragma that names a prover
\* and, optionally, a timeout or a tactic. The operators are deliberately
\* side-effect free; they only record the dispatch plan.
\* The temporal-logic rules are included for completeness and to reserve
\* their names, not because this module runs any proof steps itself.

\* Dispatch a proof obligation to the Zenon first-order prover.
ZenonDispatch == Zenon

\* Dispatch a proof obligation to Isabelle/HOL.
IsabelleDispatch == Isabelle

\* Dispatch a proof obligation to the CVC3 SMT solver.
CVC3Dispatch == CVC3

\* Dispatch a proof obligation to the Yices SMT solver.
YicesDispatch == Yices

\* Dispatch a proof obligation to the veriT SMT solver.
VeriTDispatch == VeriT

\* Dispatch a proof obligation to the Z3 SMT solver.
Z3Dispatch == Z3

\* Dispatch a proof obligation to the SPASS theorem prover.
SPASSDispatch == SPASS

\* Dispatch a proof obligation to the LS4 temporal logic prover.
LS4Dispatch == LS4

\* Temporal logic proof rules (reserved names from Lamport's TLA+ paper):
\* invariance, well-formedness, strong fairness, weak fairness, and step
\* simulation. They are theorems of the logic, not actions of this module.
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

\* Foundational set-theoretic theorems: set extensionality and the
\* non-universality of any set. These are always true, so they belong in
\* the module's property set rather than as separate actions.
SetExtensionality == TRUE
NoSetIsUniversal == TRUE

\* The module's specification is the conjunction of the two theorems.
Specification == SetExtensionality /\ NoSetIsUniversal

\* The module's initial state: there is nothing to initialize, so TRUE.
INIT == TRUE

\* The module has no actions (it is a configuration/definition module).
NEXT == TRUE

\* The module's invariant: the two foundational theorems hold.
INVARIANTS == Specification

\* The module's liveness property: the two foundational theorems hold.
PROPERTIES == Specification

====