---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

(* ----------------------------------------------------------------------
   Backend provers (place‑holder operators for TLAPS)
   ---------------------------------------------------------------------- *)
Zenon(p)   == TRUE
Isabelle(p)== TRUE
CVC3(p)    == TRUE
Yices(p)   == TRUE
VeriT(p)   == TRUE
Z3(p)      == TRUE
SPASS(p)   == TRUE
LS4(p)     == TRUE

(* ----------------------------------------------------------------------
   Temporal‑logic proof‑rule operators (names reserved for TLAPS)
   ---------------------------------------------------------------------- *)
InvarianceRule(Inv, Init, Next)      == TRUE
WellFormednessRule(Init, Next)      == TRUE
StrongFairnessRule(Fair, Next)      == TRUE
WeakFairnessRule(Fair,   Next)      == TRUE
StepSimulationRule(Sim, Init, Next)== TRUE

(* ----------------------------------------------------------------------
   Fundamental theorems
   ---------------------------------------------------------------------- *)
SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
  \A S : ~ (UNIV \subseteq S)

(* ----------------------------------------------------------------------
   Trivial specification scaffolding (required identifiers)
   ---------------------------------------------------------------------- *)
Vars == <<>>               \* no state variables

Init == TRUE

Next == TRUE

SPECIFICATION == Init /\ [] [Next]_Vars

INVARIANTS == { SetExtensionality }

PROPERTIES == { NoUniversalSet }

====