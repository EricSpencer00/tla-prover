---- MODULE TLAPS ----
EXTENDS TLC

\* ----------------------------------------------------------------------
\* Backend provers and their (placeholder) dispatch operators
\* ----------------------------------------------------------------------
CONSTANT ZenonTimeout, IsabelleTimeout, CVC3Timeout,
         YicesTimeout, VeriTTimeout, Z3Timeout,
         SPASSTimeout, LS4Timeout

Zenon(p, t)    == TRUE
Isabelle(p, t) == TRUE
CVC3(p, t)     == TRUE
Yices(p, t)    == TRUE
VeriT(p, t)    == TRUE
Z3(p, t)       == TRUE
SPASS(p, t)    == TRUE
LS4(p, t)      == TRUE

\* ----------------------------------------------------------------------
\* Temporal‑logic proof‑rule placeholders
\* ----------------------------------------------------------------------
InvarianceRule       == TRUE
WellFormednessRule  == TRUE
StrongFairnessRule  == TRUE
WeakFairnessRule    == TRUE
StepSimulationRule  == TRUE

\* ----------------------------------------------------------------------
\* Fundamental theorems
\* ----------------------------------------------------------------------
SetExtensionality ==
  \* If two sets have the same elements then they are equal
  \A S, T \in SUBSET UNIV :
     (\A x : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
  \* No set contains every possible value
  \A S : ~(\A x : x \in S)

=============================================================================