---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Universe

\* ----------------------------------------------------------------------
\* Backend prover primitives (pragmas) for TLAPS.
\* These operators are uninterpreted; they merely serve as markers for the
\* proof manager indicating which external prover should be used.
\* ----------------------------------------------------------------------
Zenon(p)   == p
Isabelle(p)== p
CVC3(p)    == p
Yices(p)   == p
VeriT(p)   == p
Z3(p)      == p
SPASS(p)   == p
LS4(p)     == p

\* ----------------------------------------------------------------------
\* Fundamental set-theoretic theorems.
\* ----------------------------------------------------------------------
SetExtensionality ==
  \A S, T \in SUBSET Universe :
    (\A x : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
  \A S \in SUBSET Universe : ~(\A x : x \in S)

\* ----------------------------------------------------------------------
\* Temporal‑logic proof‑rule names (reserved for future use).
\* The definitions are placeholders; their logical content is provided
\* by the TLAPS backend, not by this specification.
\* ----------------------------------------------------------------------
InvarianceRule        == TRUE
WellFormednessRule   == TRUE
StrongFairnessRule   == TRUE
WeakFairnessRule     == TRUE
StepSimulationRule   == TRUE

====