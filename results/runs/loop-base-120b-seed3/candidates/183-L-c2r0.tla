---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Backend prover dispatch operators (place‑holders for TLAPS pragmas)
\* ----------------------------------------------------------------------
Zenon(p) == TRUE
Isabelle(p) == TRUE
CVC3(p) == TRUE
Yices(p) == TRUE
VeriT(p) == TRUE
Z3(p) == TRUE
SPASS(p) == TRUE
LS4(p) == TRUE

\* ----------------------------------------------------------------------
\* Fundamental set theorems
\* ----------------------------------------------------------------------
SetExtensionality ==
    \A S, T \in SUBSET UNIV :
        (\A x : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
    ~(\E S \in SUBSET UNIV : \A x \in UNIV : x \in S)

\* ----------------------------------------------------------------------
\* Temporal‑logic proof rule placeholders (names reserved for TLAPS)
\* ----------------------------------------------------------------------
Invariance(P, step) == TRUE
WellFormedness(P) == TRUE
StrongFairness(P, action) == TRUE
WeakFairness(P, action) == TRUE
StepSimulation(step1, step2) == TRUE

====