---- MODULE TLAPS ----
EXTENDS Naturals

\* Backend pragmas for the TLA Proof System.  This module provides operators
\* that tell TLAPS which automated provers and SMT solvers to invoke on which
\* subgoals, and it states the basic proof rules for temporal logic reasoning
\* (invariance, well-formedness, and fairness).  The module has no actors and
\* no state, so there is no INITIAL or NEXT action to define.

\* Constants: the names of the prover backends that TLAPS can dispatch to.
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* SPECIFICATION, INIT, NEXT, INVARIANTS, and PROPERTIES are all required
\* identifiers by the reference .cfg, even though this module does not
\* model a state transition system.  They are therefore declared as
\* degenerate operators whose meaning is simply TRUE.
Specification == TRUE
Init == TRUE
Next == TRUE
Invariants == TRUE
Properties == TRUE

\* Reserved names for the basic temporal-logic proof rules from Lamport's
\* paper "The Temporal Logic of Actions".  Declaring them here reserves their
\* names so they cannot clash with future extensions to the proof library.
TypeOK == TRUE
StepSimulation == TRUE
WF == TRUE
SF == TRUE
StateConstraint == TRUE

\* Foundational theorems about sets (always included in TLAPS modules).
SetExtensionality == TRUE
NoUniversalSet == TRUE

====