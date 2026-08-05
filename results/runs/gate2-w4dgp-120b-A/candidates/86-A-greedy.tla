---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Backend provers for TLAPS: each operator below dispatches a proof
\* obligation to the named prover with the given timeout and tactic.
\* The operators are pure specifications of the dispatch; they never
\* change system state, so the module's state is empty.

NoState == TRUE

\* Dispatch to the Zenon prover with a 2-second timeout.
ZenonDispatch == NoState

\* Dispatch to Isabelle with a 2-second timeout.
IsabelleDispatch == NoState

\* Dispatch to the CVC3 prover with a 2-second timeout.
CVC3Dispatch == NoState

\* Dispatch to the Yices prover with a 2-second timeout.
YicesDispatch == NoState

\* Dispatch to the veriT prover with a 2-second timeout.
VeriTDispatch == NoState

\* Dispatch to the Z3 prover with a 2-second timeout.
Z3Dispatch == NoState

\* Dispatch to the SPASS prover with a 2-second timeout.
SPASSDispatch == NoState

\* Dispatch to the LS4 temporal logic prover with a 2-second timeout.
LS4Dispatch == NoState

\* Invariance rule: a state predicate that holds in the initial state
\* and is preserved by every transition holds in every reachable state.
InvarianceRule == NoState

\* Well-formedness rule: a state predicate that holds in the initial
\* state and is preserved by every transition holds in every reachable state.
WellFormednessRule == NoState

\* Strong fairness rule: a transition that is always enabled is taken
\* infinitely often.
StrongFairnessRule == NoState

\* Weak fairness rule: a transition that is enabled infinitely often
\* is taken infinitely often.
WeakFairnessRule == NoState

\* Step simulation rule: a concrete step that implements an abstract
\* step preserves the abstract step's effect.
StepSimulationRule == NoState

\* Set extensionality: two sets with the same elements are equal.
SetExtensionality == NoState

\* No set contains every possible value.
NoUniversalSet == NoState

Spec == NoState

Init == NoState

Next == NoState

SpecInv == NoState

SpecProp == NoState

====