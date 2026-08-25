---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Backend provers for TLAPS.  These operators are placeholders that
  allow the proof system to dispatch obligations to the named
  automated provers or SMT solvers.
-----------------------------------------------------------------*)
Zenon(p)    == p
Isabelle(p) == p
CVC3(p)     == p
Yices(p)    == p
VeriT(p)    == p
Z3(p)       == p
SPASS(p)    == p
LS4(p)      == p

(*-----------------------------------------------------------------
  Temporal‑logic proof‑rule operators (placeholders).  Their names are
  reserved for use by TLAPS; the definitions here simply return TRUE.
-----------------------------------------------------------------*)
InvarianceRule(Inv, Init, Next)      == TRUE
WellFormednessRule(Init, Next)       == TRUE
StrongFairnessRule(Fair, Next)       == TRUE
WeakFairnessRule(Fair, Next)         == TRUE
StepSimulationRule(Sim, Init, Next) == TRUE

(*-----------------------------------------------------------------
  Fundamental theorems required by the library.
-----------------------------------------------------------------*)
THEOREM SetExtensionality ==
  \A S, T : (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S : ~ (S = UNIV)

====