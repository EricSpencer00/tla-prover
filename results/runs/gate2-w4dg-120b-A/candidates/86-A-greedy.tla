---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* Backend provers for TLAPS: each operator names a prover and a timeout.
\* The operators are deliberately pure (no state change) because this
\* module is configuration infrastructure, not a concurrent system.
\* The temporal-logic proof rules below are included as reserved names
\* (invariance, well-formedness, fairness) so they cannot be reused.

Zenon(t) == "zenon " ^ t
Isabelle(t) == "isabelle " ^ t
CVC3(t) == "cvc3 " ^ t
Yices(t) == "yices " ^ t
VeriT(t) == "verit " ^ t
Z3(t) == "z3 " ^ t
SPASS(t) == "spass " ^ t
LS4(t) == "ls4 " ^ t

\* Foundational temporal-logic proof rules (reserved names only).
Invariance == "invariance rule"
WellFormedness == "well-formedness rule"
StrongFairness == "strong fairness rule"
WeakFairness == "weak fairness rule"
StepSimulation == "step simulation rule"

\* Two foundational theorems: set extensionality and the non-universality
\* of any set. They are the only properties this module asserts.
Extensionality == \A A, B \in SUBSET Nat : (\A x \in Nat : x \in A <=> x \in B) => A = B
NoSetIsUniversal == \A A \in SUBSET Nat : \E x \in Nat : x \notin A

SPECIFICATION == Extensionality /\ NoSetIsUniversal
INIT == Extensionality
NEXT == NoSetIsUniversal
INVARIANTS == Extensionality
PROPERTIES == NoSetIsUniversal

====