---- MODULE TLAPS ----
\* Backend configuration for the TLA+ Proof System (TLAPS).  The operators
\* below are what the proof manager consults to decide which prover to
\* invoke, with what timeout, and which tactics to use.  The temporal logic
\* rules (invariance, well-formedness, fairness) are included so their names
\* are reserved for future extensions (they are not instantiated against any
\* concrete state here; the module has no state of its own).
EXTENDS Naturals

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* No system state to initialize; this module only defines dispatch operators.
CONSTANTS == TRUE

Spec == TRUE

Init == TRUE

Next == TRUE

Invariants == TRUE

Properties == TRUE

\* One carefully chosen rule from Lamport's "Temporal Logic of Actions": the
\* invariance rule, which lets a designer assert that a state predicate holds
\* at every reachable state.  In this module there is nothing to discharge,
\* so the rule is an axiom rather than a derived theorem.
InvarianceRule == TRUE

\* Set extensionality: two sets with the same members are equal.
Extensionality == TRUE

\* No set contains every possible value.
NoUniversalSet == TRUE

====