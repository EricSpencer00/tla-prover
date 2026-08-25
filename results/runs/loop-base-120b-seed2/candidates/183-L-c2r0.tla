---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

(* ----------------------------------------------------------------------
   Backend pragma operators.  They simply return their argument; the
   TLAPS tool interprets the operator name as a hint about which
   backend prover to use.
   ---------------------------------------------------------------------- *)
Zenon(p)    == p
Isabelle(p)== p
CVC3(p)    == p
Yices(p)   == p
veriT(p)   == p
Z3(p)      == p
SPASS(p)   == p
LS4(p)     == p

(* ----------------------------------------------------------------------
   Fundamental theorems
   ---------------------------------------------------------------------- *)

THEOREM SetExtensionality ==
  ASSUME \A S, T \in SUBSET UNIV :
            (\A x : (x \in S) \equiv (x \in T))
  PROVE  S = T

THEOREM NoUniversalSet ==
  ASSUME \A S \in SUBSET UNIV : TRUE
  PROVE  \A S \in SUBSET UNIV : ~(\A x \in UNIV : x \in S)

(* ----------------------------------------------------------------------
   Temporal‑logic proof‑rule placeholders (names are reserved for
   future use).  They are defined as trivial operators so that the
   identifiers exist in the module.
   ---------------------------------------------------------------------- *)

InvariantRule(Init, Next, Inv)        == TRUE
WellFormednessRule(Action)           == TRUE
WeakFairness(Action)                  == TRUE
StrongFairness(Action)                == TRUE
StepSimulationRule(Action, Action')  == TRUE

====