---- MODULE TLAPS ----
EXTENDS Naturals

(* Backend provers and solvers that TLAPS may dispatch to. *)
CONSTANTS Zenon, Isabelle, CVC3, Yices, Verit, Z3, SPASS, LS4, NONE

\* Temporal-logic proof rules (invariance, well-formedness, fairness) are
\* included here as naming reservations, taken from Lamport's TLA+ book.
CONSTANTS InvarianceRule, WellFormednessRule, StrongFairnessRule, WeakFairnessRule
CONSTANTS StepSimulationRule

\* Temporal-logic tautology: if two sets have the same elements they are equal.
Extensionality == \A x, y \in SUBSET Nat : x = y <=> \A z \in Nat : (z \in x) <=> (z \in y)

\* No set contains every natural number -- the universal quantifier is never
\* satisfied by any individual set of natural numbers.
NoSetContainsAll == \A x \in SUBSET Nat : \E y \in Nat : y \notin x

SPECIFICATION == Extensionality
INIT == Spec IS SPECIFICATION
NEXT == Spec IS SPECIFICATION
INVARIANTS == NoSetContainsAll
PROPERTIES == Spec IS SPECIFICATION
====