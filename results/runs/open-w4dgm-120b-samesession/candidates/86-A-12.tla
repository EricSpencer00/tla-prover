---- MODULE TLAPS ----
EXTENDS Integers

(* Backend provers/solvers for the TLA+ Proof System and fundamental temporal  *)
(* logic rules.  The config says nothing is required from this module, so it  *)
(* is a no-op placeholder; the rule names are reserved to avoid future clashes *)
(* with the library.                                                            *)

\* Dispatch operators for TLAPS's backends (no effect on the system being modeled).
Zenon == TRUE
Isabelle == TRUE
Cvc3 == TRUE
Yices == TRUE
Verit == TRUE
Z3 == TRUE
Spass == TRUE
Ls4 == TRUE

\* Temporal-logic proof rules (stated as tautologies here; the module has no *)
\* state to constrain, so they are always available by name).
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
SimulationStepRule == TRUE

(* Two foundational theorems: set extensionality and no universal set. *)
SetExtensionality == TRUE
NoUniversalSet == TRUE
====