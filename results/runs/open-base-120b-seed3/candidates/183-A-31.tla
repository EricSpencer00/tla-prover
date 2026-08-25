---- MODULE TLAPS ----
EXTENDS Naturals, TLC

\* ----------------------------------------------------------------------
\* Backend pragma operators – placeholders for TLAPS dispatch.
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
\* Temporal‑logic proof‑rule names – reserved for future use.
\* ----------------------------------------------------------------------
Invariance(P)      == TRUE
WellFormed(P)      == TRUE
StrongFairness(P) == TRUE
WeakFairness(P)   == TRUE
StepSimulation(P) == TRUE

\* ----------------------------------------------------------------------
\* Foundational theorems required by the description.
\* ----------------------------------------------------------------------
SetExtensionality ==
  \A S, T : ( \A x : (x \in S) <=> (x \in T) ) => S = T

NoSetContainsAll ==
  \A S : ~ ( \A x : x \in S )

\* ----------------------------------------------------------------------
\* Specification skeleton – required identifiers (empty because the .cfg
\* specifies none).  They are defined so that a model checker will find
\* them.
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT          == TRUE
NEXT          == TRUE
INVARIANTS    == {}
PROPERTIES    == {}

====