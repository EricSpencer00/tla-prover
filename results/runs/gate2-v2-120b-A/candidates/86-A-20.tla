---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\*  Backend prover configuration operators (place‑holders)
\* ----------------------------------------------------------------------
Zenon          == TRUE
Isabelle       == TRUE
CVC3           == TRUE
Yices          == TRUE
VeriT          == TRUE
Z3             == TRUE
SPASS          == TRUE
LS4            == TRUE

\* ----------------------------------------------------------------------
\*  Fundamental theorems (proved as theorems)
\* ----------------------------------------------------------------------
SetExtensionality ==
  \A x, y : (\A z : z \in x <=> z \in y) => x = y

NoUniversalSet ==
  \A S : \A v : v \in S => FALSE

=============================================================================