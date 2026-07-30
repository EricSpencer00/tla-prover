---- MODULE TLAPS ----
EXTENDS Naturals

\* Backend prover invocations for TLAPS: the standard set of backends
\* supported by the TLA+ proof system, together with a fixed timeout
\* that the front end applies to each.
Pragmas == {
  "with", "zenon", "inst", "cvc3", "yices", "verit", "z3", "spass", "ls4",
  "timeout", "10"
}

\* Temporal logic proof rules, named exactly as in Lamport's TLA+
\* paper so they cannot later be introduced under a colliding name.
Rules == {
  "invariant", "wf", "sf", "stepSimulation"
}

\* Every theorem in this module has an empty proof, so the model checker
\* will vacuously treat them as true, which is intentional: the module is
\* a repository of reserved names and placeholder theorems.
Extensionality == TRUE
NoSetContainsAll == TRUE

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE

INVARIANTS == {
  Extensionality, NoSetContainsAll
}

PROPERTIES == {}
====