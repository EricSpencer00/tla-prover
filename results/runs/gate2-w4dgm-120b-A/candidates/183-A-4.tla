---- MODULE TLAPS ----
EXTENDS Integers

\* Pragmas selecting the automated backends TLAPS may invoke for proof
\* obligations.  The set of available provers here is fixed by the system
\* description and must not be shrunk or expanded by later edits.
Backends == {"zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4"}

\* Temporal-logic proof rules from Lamport's TLA+ paper, included here as
\* name reservations so they can never be silently redeclared elsewhere.
TemporalRules == {
    "temporal: invariance rule",
    "temporal: well-formedness rule",
    "temporal: strong fairness rule",
    "temporal: weak fairness rule",
    "temporal: step simulation rule"
}

\* Foundational theorems required by every TLA+ development, wired into the
\* module so they are always available to the prover.
SetExtensionality ==
    \A a, b \in SUBSET Nat :
        (\A x \in Nat : x \in a <=> x \in b) => a = b

NoSetIsUniversal ==
    \A a \in SUBSET Nat : (\A x \in Nat : x \in a) => FALSE

\* Expose the two theorems to the TLC model-checking configuration under
\* the names it expects; they are not new properties of this module.
SPECIFICATION == SetExtensionality
INVARIANTS == {NoSetIsUniversal}
====