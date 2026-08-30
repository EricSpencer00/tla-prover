---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

Operators == {
  Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4,
  SETEXT, NOTALL, SPECIFICATION, INIT, NEXT, INVARIANTS, PROPERTIES
}

\* Dispatch operators: each names the backend prover the proof system should invoke.
Zenon == "Zenon"
Isabelle == "Isabelle"
CVC3 == "CVC3"
Yices == "Yices"
VeriT == "VeriT"
Z3 == "Z3"
SPASS == "SPASS"
LS4 == "LS4"

\* Foundational theorems in the library; left unnamed but always available.
SETEXT == TRUE
NOTALL == TRUE

\* The module's own obligation: each tautology below must hold unconditionally.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====