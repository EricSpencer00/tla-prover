---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Backend provers for TLAPS
\* ----------------------------------------------------------------------
CONSTANT Values

\* Dispatch operators (place‑holders) for the various automated provers
Zenon(p)      == TRUE
Isabelle(p)   == TRUE
CVC3(p)       == TRUE
Yices(p)      == TRUE
VeriT(p)      == TRUE
Z3(p)         == TRUE
SPASS(p)      == TRUE
LS4(p)        == TRUE

\* Time‑out and tactic parameters (illustrative)
ZenonTimeout      == 10
IsabelleTimeout   == 10
CVC3Timeout       == 10
YicesTimeout      == 10
VeriTTimeout      == 10
Z3Timeout         == 10
SPASSTimeout      == 10
LS4Timeout        == 10

ZenonTactic       == "default"
IsabelleTactic    == "default"
CVC3Tactic        == "default"
YicesTactic       == "default"
VeriTTactic       == "default"
Z3Tactic          == "default"
SPASSTactic       == "default"
LS4Tactic         == "default"

\* ----------------------------------------------------------------------
\* Fundamental theorems
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  \A S, T \in SUBSET Values :
    (\A x \in Values : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S \in SUBSET Values : \E x \in Values : x \notin S

\* ----------------------------------------------------------------------
\* Temporal‑logic proof rules (names reserved for future use)
\* ----------------------------------------------------------------------
InvarianceRule(P, Init, Next) == TRUE
WellFormednessRule(P)          == TRUE
StrongFairnessRule(F)          == TRUE
WeakFairnessRule(F)            == TRUE
StepSimulationRule(Spec1, Spec2) == TRUE

====