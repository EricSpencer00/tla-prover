---- MODULE TLAPS ----
\* -------------------------------------------------
\* Backend prover operators (place‑holders for TLAPS)
\* -------------------------------------------------
Zenon(obligation) == TRUE
Isabelle(obligation) == TRUE
CVC3(obligation) == TRUE
Yices(obligation) == TRUE
VeriT(obligation) == TRUE
Z3(obligation) == TRUE
SPASS(obligation) == TRUE
LS4(obligation) == TRUE

\* -------------------------------------------------
\* Temporal‑logic proof‑rule operators (place‑holders)
\* -------------------------------------------------
Invariance(rule) == TRUE
WellFormedness(rule) == TRUE
StrongFairness(rule) == TRUE
WeakFairness(rule) == TRUE
StepSimulation(rule) == TRUE

\* -------------------------------------------------
\* Fundamental theorems
\* -------------------------------------------------
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S : \E x : x \notin S

====