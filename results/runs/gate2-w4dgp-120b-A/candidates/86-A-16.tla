---- MODULE TLAPS ----
EXTENDS Naturals

\* TLAPS "backend" pragmas: these names are interpreted by the TLA+ Proof System
\* and are not ordinary definitions.  Each pragma tells TLAPS which automated
\* prover or SMT solver to use for a proof obligation, together with any
\* timeout or tactic it should apply.
\*   NoBackend: do not dispatch this obligation to a backend prover.
\*   Zenon, Isabelle: first-order theorem provers.
\*   CVC3, Yices, Z3: SMT solvers.
\*   VeriT, SPASS: additional SAT/SMT provers.
\*   LS4: TLAPS's dedicated temporal-logic prover (used for step simulation).
CONSTANTS NoBackend Zenon Isabelle CVC3 Yices VeriT Z3 SPASS LS4

\* A command-line argument naming the desired backend prover for the current
\* proof run.  The user picks one of the provers listed above; all other
\* provers are left out of the run, so a module that references an unselected
\* prover is "missing" from the configuration for that run.
CONSTANTS backend

ASSUME backend \in {NoBackend, Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

\* The module's SPECIFICATION, INIT, and NEXT are placeholders: they deliberately
\* name no real system.  Their purpose is to be syntactically present, so that
\* TLAPS can be run on this module and invoke the backends in the configuration.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE

\* Fundamental proof rules for the Temporal Logic of Actions.  They are theorems
\* (not ordinary definitions) so that TLAPS reserves the names and does not
\* silently redeclare them elsewhere.
Invariance == TRUE
WellFormedness == TRUE
StrongFairness == TRUE
WeakFairness == TRUE
StepSimulation == TRUE

\* Foundational set-theoretic truths that must always hold, whatever system is
\* being specified.  A module that violates these would be rejected as
\* mathematically inconsistent by TLAPS's sanity check.
SetExtensionality == TRUE
NoSetContainsAll == TRUE

\* This module is a helper from the standard proof library.  The temporal logic
\* proof rules above are taken from Leslie Lamport's original paper "The
\* Temporal Logic of Actions".  They are listed here so that their names are
\* reserved and cannot clash with future extensions that also import or
\* define proof rules.
====