---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Backend prover placeholders (used by TLAPS for dispatching proof steps)
\* ----------------------------------------------------------------------
Zenon(expr) == TRUE
Isabelle(expr) == TRUE
CVC3(expr) == TRUE
Yices(expr) == TRUE
VeriT(expr) == TRUE
Z3(expr) == TRUE
SPASS(expr) == TRUE
LS4(expr) == TRUE

\* ----------------------------------------------------------------------
\* Fundamental theorems required by the description
\* ----------------------------------------------------------------------
SetExtensionality ==
  \A S, T : ( \A x : (x \in S) <=> (x \in T) ) => S = T

NoUniversalSet ==
  \A S : \E x : x \notin S

\* ----------------------------------------------------------------------
\* Trivial system definition (no state variables, no actions)
\* ----------------------------------------------------------------------
INIT == TRUE
NEXT == TRUE

SPECIFICATION == INIT /\ [] [NEXT]_<<>>

INVARIANTS == {}
PROPERTIES == {}

====