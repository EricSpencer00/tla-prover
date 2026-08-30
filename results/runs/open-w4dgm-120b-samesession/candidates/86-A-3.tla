---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

ProofBackends == {Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4}

SPECIFICATION == "TLAPS specification with backends and temporal rules"
INIT == "Initialize the TLAPS proof state"
NEXT == "Advance by dispatching an obligation to a backend"
INVARIANTS == "Temporal proof rules (invariance, fairness) hold"
PROPERTIES == "Set extensionality and the non-universal set property"
====