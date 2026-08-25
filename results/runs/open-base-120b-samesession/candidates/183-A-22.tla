---- MODULE TLAPS ----
EXTENDS TLC, FiniteSets, Sequences, Naturals

\* ----------------------------------------------------------------------
\* Backend dispatch operators (pragmas for TLAPS)
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
\* Temporal‑logic proof‑rule placeholders
\* ----------------------------------------------------------------------
InvarianceRule(Inv, Next)      == TRUE
WellFormednessRule(Init, Next)== TRUE
StrongFairnessRule(Fair, Next)== TRUE
WeakFairnessRule(Fair, Next)  == TRUE
StepSimulationRule(Sim, Next) == TRUE

\* ----------------------------------------------------------------------
\* Fundamental theorems
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) \iff (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S \in SUBSET UNIV : ~(\A x \in UNIV : x \in S)

\* ----------------------------------------------------------------------
\* Trivial state for model‑checking purposes
\* ----------------------------------------------------------------------
VARIABLES dummy

Init == dummy = {}
Next == UNCHANGED dummy

\* ----------------------------------------------------------------------
\* Required top‑level identifiers
\* ----------------------------------------------------------------------
SPECIFICATION == Init /\ [][Next]_<<dummy>>
INIT == Init
NEXT == Next
INVARIANTS == {SetExtensionality, NoUniversalSet}
PROPERTIES == {}

====