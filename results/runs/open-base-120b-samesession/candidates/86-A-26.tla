---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Universe

\* ----------------------------------------------------------------------
\* Backend provers (place‑holder definitions for TLAPS pragmas)
\* ----------------------------------------------------------------------
Zenon   == TRUE
Isabelle == TRUE
CVC3    == TRUE
Yices   == TRUE
VeriT   == TRUE
Z3      == TRUE
SPASS   == TRUE
LS4     == TRUE

\* ----------------------------------------------------------------------
\* Temporal‑logic proof rules (place‑holder definitions)
\* ----------------------------------------------------------------------
Invariance      == TRUE
WellFormedness  == TRUE
StrongFairness  == TRUE
WeakFairness    == TRUE
StepSimulation  == TRUE

\* ----------------------------------------------------------------------
\* Fundamental theorems
\* ----------------------------------------------------------------------
SetExtensionality ==
  \A S, T \in SUBSET Universe :
    (\A x : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
  \A S \in SUBSET Universe :
    ~(\A x \in Universe : x \in S)

====