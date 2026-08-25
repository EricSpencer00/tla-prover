---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*-------------------------------------------------------------------*)
(* Backend pragmas for TLAPS                                           *)
(*-------------------------------------------------------------------*)
Zenon(p)      == p
Isabelle(p)   == p
CVC3(p)       == p
Yices(p)      == p
VeriT(p)      == p
Z3(p)         == p
SPASS(p)      == p
LS4(p)        == p

(*-------------------------------------------------------------------*)
(* Temporal‑logic proof‑rule placeholders                               *)
(*-------------------------------------------------------------------*)
InvarianceRule(P)          == TRUE
WellFormednessRule(P)      == TRUE
StrongFairnessRule(P)      == TRUE
WeakFairnessRule(P)        == TRUE
StepSimulationRule(P, Q)  == TRUE

(*-------------------------------------------------------------------*)
(* Fundamental theorems                                               *)
(*-------------------------------------------------------------------*)
THEOREM SetExtensionality ==
  ∀ S, T ∈ SUBSET UNIV :
    (∀ x : (x ∈ S) ⇔ (x ∈ T)) => S = T

THEOREM NoUniversalSet ==
  ∀ S : ¬ (∀ x : x ∈ S)

====