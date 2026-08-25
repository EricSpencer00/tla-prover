---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Backend prover identifiers (used as arguments to TLAPS pragmas)
\* ----------------------------------------------------------------------
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Optional timeout constants (in seconds) for each backend
ZenonTimeout   == 10
IsabelleTimeout == 10
CVC3Timeout    == 10
YicesTimeout   == 10
VeriTTimeout   == 10
Z3Timeout      == 10
SPASSTimeout   == 10
LS4Timeout     == 10

\* ----------------------------------------------------------------------
\* TLAPS backend‑dispatch operators (place‑holders – the proof system
\* interprets them specially; they return TRUE so the specification
\* remains well‑formed.
\* ----------------------------------------------------------------------
Zenon(proof)       == TRUE
Isabelle(proof)    == TRUE
CVC3(proof)        == TRUE
Yices(proof)       == TRUE
VeriT(proof)       == TRUE
Z3(proof)          == TRUE
SPASS(proof)       == TRUE
LS4(proof)         == TRUE

\* ----------------------------------------------------------------------
\* Fundamental set‑theoretic theorems
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
    \A S, T \in SUBSET UNIV :
        (\A x \in UNIV : (x \in S) \iff (x \in T)) => S = T

THEOREM NoUniversalSet ==
    \A S \in SUBSET UNIV : \E x \in UNIV : x \notin S

\* ----------------------------------------------------------------------
\* Temporal‑logic proof rules (names reserved for future use)
\* ----------------------------------------------------------------------
InvariantRule(P, Init, Next) ==
    /\ Init => P
    /\ [][Next]_<<>> => []P

WellFormednessRule(Act) == TRUE

StrongFairnessRule(P, Act) == TRUE

WeakFairnessRule(P, Act) == TRUE

StepSimulationRule(Src, Tgt) == TRUE

\* ----------------------------------------------------------------------
\* End of TLAPS configuration module
\* ----------------------------------------------------------------------
====