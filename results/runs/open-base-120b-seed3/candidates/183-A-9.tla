---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Configuration constants (left uninterpreted; values supplied by the model)
\* ----------------------------------------------------------------------
CONSTANT Universe
CONSTANT ZenonTimeout, IsabelleTimeout, CVC3Timeout, YicesTimeout,
         VeriTTimeout, Z3Timeout, SPASSTimeout, LS4Timeout

\* ----------------------------------------------------------------------
\* Backend prover dispatch operators (place‑holders for TLAPS pragmas)
\* ----------------------------------------------------------------------
Zenon(expr, timeout) == TRUE
Isabelle(expr, timeout) == TRUE
CVC3(expr, timeout) == TRUE
Yices(expr, timeout) == TRUE
VeriT(expr, timeout) == TRUE
Z3(expr, timeout) == TRUE
SPASS(expr, timeout) == TRUE
LS4(expr, timeout) == TRUE

\* ----------------------------------------------------------------------
\* Fundamental theorems
\* ----------------------------------------------------------------------
SetExtensionality ==
  \A S, T \in SUBSET Universe :
    (\A x \in Universe : (x \in S) \iff (x \in T)) => S = T

NoUniversalSet ==
  \A S \in SUBSET Universe : S # Universe

\* ----------------------------------------------------------------------
\* Temporal‑logic proof‑rule names (reserved for future use)
\* ----------------------------------------------------------------------
InvarianceRule(p) == TRUE
WellFormednessRule(p) == TRUE
StrongFairnessRule(p) == TRUE
WeakFairnessRule(p) == TRUE
StepSimulationRule(p) == TRUE

====