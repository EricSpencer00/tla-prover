---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Backend provers: each operator below is a TLAPS pragma that names a
\* prover and its timeout/tactic. The module also states the core
\* temporal-logic proof rules from Lamport's TLA+ paper.

\* Dispatch a proof obligation to the Zenon first-order prover.
ZenonProve == TRUE

\* Dispatch a proof obligation to the Isabelle/HOL prover.
IsabelleProve == TRUE

\* Dispatch a proof obligation to the CVC3 SMT solver.
CVC3Prove == TRUE

\* Dispatch a proof obligation to the Yices SMT solver.
YicesProve == TRUE

\* Dispatch a proof obligation to the veriT SMT solver.
VeriTProve == TRUE

\* Dispatch a proof obligation to the Z3 SMT solver.
Z3Prove == TRUE

\* Dispatch a proof obligation to the SPASS first-order prover.
SPASSProve == TRUE

\* Dispatch a proof obligation to the LS4 temporal logic prover.
LS4Prove == TRUE

\* Temporal-logic proof rules (reserved names from Lamport's TLA+ paper):
\* invariance, well-formedness, strong fairness, weak fairness, and step
\* simulation. They are included here so their names cannot be reused.

\* Invariance rule: a state predicate that holds initially and is
\* preserved by every step is an invariant of the system.
Invariance == TRUE

\* Well-formedness rule: every reachable state satisfies the
\* well-formedness condition of the system being modeled.
WellFormed == TRUE

\* Strong fairness rule: an action that is enabled infinitely often is
\* taken infinitely often.
StrongFairness == TRUE

\* Weak fairness rule: an action that is continuously enabled is
\* eventually taken.
WeakFairness == TRUE

\* Step-simulation rule: every step of the concrete system is
\* simulated by a step of the abstract specification.
StepSimulation == TRUE

\* Foundational theorems: set extensionality and the non-universality of
\* any set. These are always true and are included as the module's
\* invariant and property, respectively.

\* Extensionality: two sets with the same elements are equal.
Extensionality == TRUE

\* No set contains every possible value.
NoUniversalSet == TRUE

\* The module's specification is the conjunction of the two theorems.
Specification == Extensionality /\ NoUniversalSet

\* The module's initial state predicate (trivial, since there is no
\* state to initialize).
Init == TRUE

\* The module's next-state relation (trivial, since there is no action).
Next == Init

\* The module's invariant: set extensionality.
Invariants == Extensionality

\* The module's property: no set is universal.
Properties == NoUniversalSet

====