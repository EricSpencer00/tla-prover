---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  backend, timeout, tactic, provers

\* Backend pragmas: no state, only configuration operators for TLAPS.
\* Each operator returns FALSE (a proof obligation) guarded by a side-effecting
\* call to a backend prover; the call is never actually executed in the model.
NoOp == FALSE

Zenon == NoOp
Isabelle == NoOp
CVC3 == NoOp
Yices == NoOp
Verit == NoOp
Z3 == NoOp
SPASS == NoOp
LS4 == NoOp

\* Temporal logic proof rules, reserved names from Lamport's TLA+ paper.
Invariance == NoOp
WellFormed == NoOp
StrongFairness == NoOp
WeakFairness == NoOp
StepSimulation == NoOp

\* Foundational set-theoretic theorems, included to reserve their names.
SetExtensionality == NoOp
NoUniversalSet == NoOp

Specification == NoOp
Init == NoOp
Next == NoOp
Invariants == NoOp
Properties == NoOp

====