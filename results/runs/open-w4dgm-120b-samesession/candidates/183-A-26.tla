---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

SPECIFICATION == "TLAPS specification of backend provers and temporal logic rules"
INIT == "initial proof state"
NEXT == "next proof step"
INVARIANTS == "invariance and well-formedness rules"
PROPERTIES == "safety and fairness properties"

====