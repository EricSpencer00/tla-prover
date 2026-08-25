---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(*----------------------------------------------------------------------
  Backend provers for TLAPS.
  Each operator simply returns its argument; the real meaning is given
  by the TLAPS pragmas that interpret these names.
----------------------------------------------------------------------*)
Zenon(p)     == p
Isabelle(p)  == p
CVC3(p)      == p
Yices(p)     == p
VeriT(p)     == p
Z3(p)        == p
SPASS(p)     == p
LS4(p)       == p

(*----------------------------------------------------------------------
  Temporal‑logic proof rules (place‑holders).
----------------------------------------------------------------------*)
Invariance(P, Init, Next)    == TRUE
WellFormedness(P)            == TRUE
StrongFairness(F)            == TRUE
WeakFairness(F)              == TRUE
StepSimulation(Pre, Post)   == TRUE

(*----------------------------------------------------------------------
  Fundamental theorems.
----------------------------------------------------------------------*)
THEOREM SetExtensionality ==
  ∀ S, T ∈ SUBSET UNIV :
    (∀ x ∈ UNIV : (x ∈ S) <=> (x ∈ T)) => S = T

THEOREM NoUniversalSet ==
  ∀ S : ¬ (∀ x ∈ UNIV : x ∈ S)

====