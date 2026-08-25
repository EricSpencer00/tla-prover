---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Backend provers for TLAPS.  The arguments are placeholders; the
\* definitions are merely truth values so that the identifiers exist.
\* ----------------------------------------------------------------------
Zenon(obl, timeout)   == TRUE
Isabelle(obl, timeout) == TRUE
CVC3(obl, timeout)    == TRUE
Yices(obl, timeout)   == TRUE
VeriT(obl, timeout)   == TRUE
Z3(obl, timeout)      == TRUE
SPASS(obl, timeout)   == TRUE
LS4(obl, timeout)     == TRUE

\* ----------------------------------------------------------------------
\* Temporal‑logic proof rules (names reserved for future use).
\* ----------------------------------------------------------------------
InvariantRule(P)          == TRUE
WellFormednessRule(phi)   == TRUE
StrongFairnessRule(P, Q)  == TRUE
WeakFairnessRule(P, Q)    == TRUE
StepSimulationRule(A, B)  == TRUE

\* ----------------------------------------------------------------------
\* Fundamental theorems required by the description.
\* ----------------------------------------------------------------------
SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
  \A S : ~ (UNIV \subseteq S)

=============================================================================