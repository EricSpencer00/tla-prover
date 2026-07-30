---- MODULE TLAPS ----
EXTENDS Naturals

\* Backend provers for TLAPS: the operators below do not invoke anything here
\* -- they simply name the provers that TLAPS may dispatch a proof to.
CONSTANTS Zenon, Isabelle, CVC3, Yices, Verit, Z3, SPASS, LS4

\* Temporal logic proof rules (invariance, well-formedness, fairness, etc.)
\* declared here so the library knows these names and reserves them.
CONSTANTS InvarianceRule, WeakFairnessRule, StrongFairnessRule

\* The module's SPECIFICATION, INIT, NEXT, INVARIANTS and PROPERTIES are all
\* no-ops, since there is literally nothing to model: the spec exists only to
\* hold these reserved names. Any constant may stand in for the true rule.
Spec == TRUE
Init == TRUE
Next == TRUE
Invariants == TRUE
Properties == TRUE
====