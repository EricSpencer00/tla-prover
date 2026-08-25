---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Backend provers for TLAPS.  These operators are placeholders that the
\* proof manager recognizes as directives to dispatch sub‑goals to the
\* indicated automated theorem provers or SMT solvers.
\* ----------------------------------------------------------------------
Zenon(p)    == p
Isabelle(p) == p
CVC3(p)     == p
Yices(p)    == p
VeriT(p)    == p
Z3(p)       == p
SPASS(p)    == p
LS4(p)      == p

\* ----------------------------------------------------------------------
\* Temporal logic proof rules (place‑holder definitions).  Their names are
\* reserved so that future modules can refer to them without clash.
\* ----------------------------------------------------------------------
InvarianceRule(Inv, Init, Next) == TRUE
WellFormednessRule(Init, Next)   == TRUE
WeakFairnessRule(Action)         == TRUE
StrongFairnessRule(Action)       == TRUE
StepSimulationRule(Sim)          == TRUE

\* ----------------------------------------------------------------------
\* Fundamental theorems required by the specification.
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S : \E x \in UNIV : x \notin S

\* ----------------------------------------------------------------------
\* Standard spec identifiers required by the configuration (none are
\* explicitly required, but we provide the usual placeholders).
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT          == TRUE
NEXT          == TRUE
INVARIANTS    == {}
PROPERTIES    == {}

====