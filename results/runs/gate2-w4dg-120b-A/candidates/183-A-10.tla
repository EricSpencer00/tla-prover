---- MODULE TLAPS ----
EXTENDS Naturals

\* This module provides TLAPS backend pragmas and declares foundational temporal
\* logic proof rules as reserved operators. It carries no state of its own.
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4, Timeout

Spec == "Main"
Init == "Start"
Next == "Step"
Invariants == "TypeOK"
Properties == "NoSetIsUniversal"
====