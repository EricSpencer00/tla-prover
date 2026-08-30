---- MODULE TLAPS ----
EXTENDS Integers

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

SpecOps == {"zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4"}

Specification == "TLAPS Standard Configuration for Temporal Logic Backends"
INIT == "Initial state"
NEXT == "Dispatch next obligation"
INVARIANTS == "Invariance rule"
PROPERTIES == "Well-formedness and fairness rule"

\* Extensionality: two sets with identical elements are equal.
SetExtensionality ==
  \A A, B \in SUBSET Nat :
    (\A x \in Nat : (x \in A) <=> (x \in B)) => (A = B)

\* No set contains every value.
NoUniversalSet ==
  \A S \in SUBSET Nat : (~ \A x \in Nat : x \in S)

====