---- MODULE TLAPS ----
EXTENDS TLC

\* ----------------------------------------------------------------------
\* Backend prover placeholders (used only as names in TLAPS proofs)
\* ----------------------------------------------------------------------
CONSTANT Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* ----------------------------------------------------------------------
\* Specification skeleton (no state, no actions)
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

\* ----------------------------------------------------------------------
\* Fundamental theorems required by the description
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  \A S, T : (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S : ~(\A x : x \in S)

====