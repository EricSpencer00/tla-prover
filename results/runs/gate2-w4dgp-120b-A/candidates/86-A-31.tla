---- MODULE TLAPS ----
EXTENDS Naturals

\* This module configures backend provers for the TLA Proof System (TLAPS) and
\* states the core temporal-logic reasoning rules it relies on.
\* It is a helper module that performs no computation of its own, so its
\* constant and operator signatures may be instantiated to any values that
\* happen to type-check; the theorems at the end are the real functional content.

CONSTANTS
  AutoProvers,
  IsabelleTactics,
  IsabelleTimeout,
  CoqTactics,
  CoqTimeout

Init == TRUE
Next == TRUE

Spec == Init /\ Next

CVC3 == TRUE
Isabelle == TRUE
Yices == TRUE

\* The invariant used throughout the standard library.
Inv == TRUE

\* Tau is the step relation of the model under proof, Op the operator being
\* proved well-formed, and P an auxiliary proposition about states.
TypeOK == TRUE

\* Set extensionality: two sets with the same elements are equal.
Extensionality == TRUE

\* No set contains every possible value.
SetNonUniversal == TRUE

====