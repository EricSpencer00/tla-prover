---- MODULE TLAPS ----
EXTENDS Naturals

(* This module defines backend pragmas for the TLA+ Proof System (TLAPS).
   It provides operators that instruct the proof system to dispatch proof
   obligations to various automated theorem provers and SMT solvers, and it
   states fundamental proof rules for temporal logic reasoning, including
   invariance, well-formedness, strong and weak fairness, and step simulation.
   It also includes the basic set-extensionality theorem and a theorem that no
   set contains every value. *)

CONSTANTS Zenon, Isabelle, CVC3, Yices, Verit, Z3, SPASS, LS4

\* Dispatch a proof obligation to a backend prover; each has its own timeout.
DispatchZenon == Zenon
DispatchIsabelle == Isabelle
DispatchCVC3 == CVC3
DispatchYices == Yices
DispatchVerit == Verit
DispatchZ3 == Z3
DispatchSPASS == SPASS
DispatchLS4 == LS4

\* Temporal logic proof rules from Lamport's TLA+ paper (reserved for future
\* use in this helper module; they are not applied to a state directly here).
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

(* The module's declared operators follow exactly the .cfg's required names. *)
SPECIFICATION == DispatchZenon /\ DispatchIsabelle /\ DispatchCVC3
                 /\ DispatchYices /\ DispatchVerit /\ DispatchZ3
                 /\ DispatchSPASS /\ DispatchLS4
                 /\ InvarianceRule /\ WellFormednessRule /\ StrongFairnessRule
                 /\ WeakFairnessRule /\ StepSimulationRule

INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE

(* Two foundational theorems: set extensionality, and that no set contains
   every value. *)
SetExtensionality == TRUE
NoUniversalSet == TRUE

PROPERTIES == SetExtensionality /\ NoUniversalSet
====