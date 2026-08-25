---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Backend pragma operators (placeholders for TLAPS configuration)
\* ----------------------------------------------------------------------
Zenon(p)    == TRUE
Isabelle(p) == TRUE
CVC3(p)     == TRUE
Yices(p)    == TRUE
VeriT(p)    == TRUE
Z3(p)       == TRUE
SPASS(p)    == TRUE
LS4(p)      == TRUE

\* ----------------------------------------------------------------------
\* Temporal logic proof‑rule operators (placeholders)
\* ----------------------------------------------------------------------
Invariance(rule)       == TRUE
WellFormedness(rule)   == TRUE
StrongFairness(rule)   == TRUE
WeakFairness(rule)     == TRUE
StepSimulation(rule)   == TRUE

\* ----------------------------------------------------------------------
\* Fundamental theorems required by the description
\* ----------------------------------------------------------------------
SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
  ~(\E S : UNIV \subseteq S)

====