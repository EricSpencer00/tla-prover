---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Backend provers for TLAPS.  These operators are placeholders that the
\* proof manager recognizes as directives to dispatch the given proof
\* obligation to the indicated automated prover or SMT solver.
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
\* Temporal‑logic proof‑rule operators.  The bodies are trivial because the
\* actual reasoning is performed by the TLAPS back‑end; the definitions
\* merely reserve the names.
\* ----------------------------------------------------------------------
InvarianceRule(P)          == TRUE
WellFormednessRule(P)      == TRUE
StrongFairnessRule(P)      == TRUE
WeakFairnessRule(P)        == TRUE
StepSimulationRule(P, Q)   == TRUE

\* ----------------------------------------------------------------------
\* Fundamental set‑theoretic theorems that are always available.
\* ----------------------------------------------------------------------
SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A a : (a \in S) \<=> (a \in T)) => S = T

NoUniversalSet ==
  \A S \in SUBSET UNIV : S # UNIV

====