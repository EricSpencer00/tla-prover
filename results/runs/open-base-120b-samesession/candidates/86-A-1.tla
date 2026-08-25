---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* -------------------------------------------------
\* Backend prover placeholders for TLAPS
\* -------------------------------------------------
Zenon(p) == TRUE
Isabelle(p) == TRUE
CVC3(p) == TRUE
Yices(p) == TRUE
veriT(p) == TRUE
Z3(p) == TRUE
SPASS(p) == TRUE
LS4(p) == TRUE

\* -------------------------------------------------
\* Temporal‑logic proof‑rule placeholders
\* -------------------------------------------------
InvariantRule(P) == TRUE
WellFormednessRule(P) == TRUE
StrongFairnessRule(F) == TRUE
WeakFairnessRule(F) == TRUE
StepSimulationRule(S) == TRUE

\* -------------------------------------------------
\* Fundamental theorems
\* -------------------------------------------------
THEOREM SetExtensionality ==
    \A S, T :
        (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoSetContainsAll ==
    \A S : \E x : x \notin S

====