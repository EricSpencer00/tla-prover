---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

\* Backend prover configuration for TLAPS: each operator names a prover or
\* proof rule; this module has no system state of its own.
CONSTANTS Zenon, Isabelle, SmtCvc3, SmtYices, SmtVeriT, SmtZ3, SmtSpass, Ls4

Spec == "compactness"

Init == Spec

Next == Spec

Invariants == Spec

Properties == Spec

====