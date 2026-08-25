---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

(* placeholder for the set of state variables used in temporal operators *)
vars == {}

(* Backend prover operators – they simply return the obligation unchanged,
   serving as placeholders for TLAPS pragmas. *)
Zenon(obligation) == obligation
Isabelle(obligation) == obligation
CVC3(obligation) == obligation
Yices(obligation) == obligation
VeriT(obligation) == obligation
Z3(obligation) == obligation
SPASS(obligation) == obligation
LS4(obligation) == obligation

(* Temporal‑logic proof‑rule operators *)

InvarianceRule(Init, Next, Inv) ==
  /\ Init => Inv
  /\ Inv /\ [Next]_vars => Inv

WellFormednessRule(expr) == TRUE

StrongFairnessRule(Proc, FairCond) == TRUE

WeakFairnessRule(Proc, FairCond) == TRUE

StepSimulationRule(step1, step2) == TRUE

(* Fundamental theorems *)

SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
  \A S : ~ (UNIV \subseteq S)

====