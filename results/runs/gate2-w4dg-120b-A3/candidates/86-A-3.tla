---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  NONE
  Zenon
  Isabelle
  CVC3
  Yices
  veriT
  Z3
  SPASS
  LS4
  Verifier

\* These names are reserved for proof rules appearing in Lamport's TLA paper.
\* Reserving them here makes future revisions of the library safe against clashes.
\* No rule is actually implemented in this configuration-only module.
\* The set-extensionality theorem and the "no-universal-set" theorem are
\* included as well-founded logical facts that the proof system may invoke.
NoSetContainsAllValues == \A x \in {0, 1} : x \notin {0, 1}

SetExtensionality ==
  \A S, T \in SUBSET {0, 1} : (\A x \in {0, 1} : (x \in S) <=> (x \in T)) => S = T

SPECIFICATION == "NoSpec"
INIT == "NoInit"
NEXT == "NoNext"
INVARIANTS == "NoInvariants"
PROPERTIES == "NoProperties"
====