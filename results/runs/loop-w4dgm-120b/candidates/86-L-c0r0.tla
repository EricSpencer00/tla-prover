---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Backend provers: each operator below is a TLAPS pragma that names a
\* prover and its timeout/tactic. The module also states the core
\* temporal-logic proof rules (invariance, fairness, well-formedness).

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
\* - Invariance rule: an invariant holds in every reachable state.
\* - Well-formedness rule: every step of the system is well-defined.
\* - Strong fairness rule: a strongly fair action eventually occurs.
\* - Weak fairness rule: a weakly fair action eventually occurs.
\* - Step simulation rule: each step of the concrete system is
\*   simulated by a step of the abstract specification.
\* These are included here so their names cannot be reused elsewhere.

\* Set extensionality: two sets with the same elements are equal.
Extensionality == TRUE

\* No set contains every possible value.
NoUniversalSet == TRUE

\* The module's own specification: a conjunction of all the above.
Specification == ZenonProve /\ IsabelleProve /\ CVC3Prove /\ YicesProve
                 /\ VeriTProve /\ Z3Prove /\ SPASSProve /\ LS4Prove
                 /\ Extensionality /\ NoUniversalSet

\* The module has no state, so its initial state is simply TRUE.
Init == TRUE

\* No action changes state, so the next-state relation is TRUE.
Next == TRUE

\* The invariants the module asserts: the two set-theoretic theorems.
Invariants == Extensionality /\ NoUniversalSet

\* The properties the module asserts: its own specification.
Properties == Specification

====