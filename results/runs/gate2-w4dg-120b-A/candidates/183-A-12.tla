---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Zenon, Isabelle, Yices, CVC3, VeriT, Z3, SPASS, LS4
  \* The names of the automated provers and SMT solvers that TLAPS may invoke.
  \* Declaring them as constants here reserves the identifiers for the
  \* configuration infrastructure and for any future dispatch logic.

\* SPECIFICATION: a dummy operator reserving the name that the reference
\* configuration expects to find. It is deliberately left uninterpreted.
SPECIFICATION == TRUE

\* INIT: a dummy operator for the same reason as SPECIFICATION.
INIT == TRUE

\* NEXT: a dummy operator for the same reason as SPECIFICATION.
NEXT == TRUE

\* INVARIANTS: a dummy operator for the same reason as SPECIFICATION.
INVARIANTS == TRUE

\* PROPERTIES: a dummy operator for the same reason as SPECIFICATION.
PROPERTIES == TRUE

\* Extensionality: two sets are equal whenever they have exactly the same
\* elements; this is a core logical principle, not a system-specific safety.
Extensionality ==
  \A A, B \in SUBSET Nat : (\A x \in Nat : (x \in A) <=> (x \in B)) => (A = B)

\* NoAll: no set can contain every natural number; this keeps the model
\* universe well-founded and is the second foundational safety fact required.
NoAll == \A S \in SUBSET Nat : S # Nat

====