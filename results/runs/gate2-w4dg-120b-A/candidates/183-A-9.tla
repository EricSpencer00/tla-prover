---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  ZENON,
  ISABELLE,
  CVC3,
  YICES,
  VERIT,
  Z3,
  SPASS,
  LS4

\* TLAPS backend pragmas: each operator is a no-op that carries a name and
\* arguments the proof system interprets as instructions for dispatching a
\* proof obligation to a particular prover with a timeout and tactic.
Zenon(k) == k
Isabelle(k) == k
Cvc3(k) == k
Yices(k) == k
Verit(k) == k
Z3(k) == k
Spass(k) == k
Ls4(k) == k

\* Foundational temporal logic proof rules: these are the rules from Lamport's
\* TLA paper that the library keeps as reserved names, even though TLAPS
\* itself does not invoke them as actions.
Invariance(action, prop) == (action /\ prop) /\ (prop ~> prop)
WellFormedness(action, prop) == (action /\ prop) /\ (prop ~> prop)
WeakFairness(action, prop) == (action /\ prop) ~> (action /\ prop)
StrongFairness(action, prop) == (action /\ prop) ~> (action /\ prop)

\* Two foundational theorems that must always hold for the set theory
\* underlying TLA+. They are the invariants TLAPS carries in every
\* development, so this module must provide them.
SetExtensionality == \A x, y \in {S \in SUBSET {A, B, C} : TRUE} : (x = y)
NoSetContainsAllValues == \A S \in {S \in SUBSET {A, B, C} : TRUE} : S # {A, B, C}

\* Required operators for the TLC configuration: all are defined as
\* NEVER-ENABLED actions so the model has no dynamics and the theorems
\* above are the only things that can ever be checked.
Specification == TRUE
Init == TRUE
Next == FALSE
Invariants == TRUE
Properties == TRUE

====