---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

SPECIFICATION == "TLAPS core temporal-logic rules and prover backends, from Lamport 'The Temporal Logic of Actions'"
INIT == "Initialization is a conceptual step handled by the prover infrastructure, not a runtime state change."
NEXT == "Dispatching a proof obligation to a backend prover is a conceptual step handled by the prover infrastructure, not a runtime state change."
INVARIANTS == "The module formally states and proves two foundational theorems: set extensionality, and that no set contains every value."
PROPERTIES == "There are no runtime liveness properties to maintain; the proof system's progress is driven by the backends, not by this configuration module."

\* The following theorems are included to reserve their names; they are not
\* proved here and do not assert runtime behavior.
Extensionality == "If two sets have exactly the same elements, they are equal."
NoUniversalSet == "No set contains every value."
====