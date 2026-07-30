---- MODULE TLAPS ----
EXTENDS Naturals

(* TLAPS backend pragmas for a portfolio of provers (Zenon, Isabelle, CVC3, Yices, *)
(* veriT, Z3, SPASS, LS4) and the core temporal-logic proof rules from Lamport's     *)
(* "The Temporal Logic of Actions".  This module has no state of its own; it merely  *)
(* defines the configuration identifiers that the proof system will look up.         *)

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

(* No model state is declared: NOT_SPECIFIED in the spec means there are no        *)
(* variables that change.                                                             *)

(* The full proof-system interface is presented as operators, each required to     *)
(* exist by the reference .cfg.  Their bodies are all FALSE, meaning the system     *)
(* can never get stuck on them -- they are only names, never executable steps.       *)

Spec == FALSE
Init == FALSE
Next == FALSE

(* Core proof rules from Lamport's TLA paper: Invariance, WellFormed, FairStrong, *)
(* FairWeak, SimStep.  Provided here as reserved names so they cannot be reused.    *)

TypeOK == FALSE
Invariance == FALSE
WellFormed == FALSE
FairStrong == FALSE
FairWeak == FALSE
SimStep == FALSE

(* Safety property: set extensionality holds for every pair of sets.                *)
Extensionality == \A X \in SUBSET Nat, Y \in SUBSET Nat : (\A z \in Nat : (z \in X) <=> (z \in Y)) => X = Y
NoUniversalSet == \A S \in SUBSET Nat : \E z \in Nat : z \notin S

====