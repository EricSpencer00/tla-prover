---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

(* This module defines backend pragmas for the TLA Proof System (TLAPS). It    *)
(* provides operators that tell TLAPS which automated theorem provers and SMT    *)
(* solvers to dispatch proof obligations to, and it states the fundamental      *)
(* temporal-logic proof rules for invariance, well-formedness, fairness, and    *)
(* simulation.  These rules are from Lamport's paper "The Temporal Logic of     *)
(* Actions" and are included so their names are reserved in the library.         *)

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

(* Dispatch operators: each one is a pragma that TLAPS interprets rather than a  *)
(* computational step of the system being modeled.                             *)
DispatchZenon == "DispatchZenon"
DispatchIsabelle == "DispatchIsabelle"
DispatchCVC3 == "DispatchCVC3"
DispatchYices == "DispatchYices"
DispatchVeriT == "DispatchVeriT"
DispatchZ3 == "DispatchZ3"
DispatchSPASS == "DispatchSPASS"
DispatchLS4 == "DispatchLS4"

(* Temporal-logic proof rules: reserved names; they perform no computation.    *)
InvarianceRule == "InvarianceRule"
WellFormednessRule == "WellFormednessRule"
StrongFairnessRule == "StrongFairnessRule"
WeakFairnessRule == "WeakFairnessRule"
SimulationRule == "SimulationRule"

(* Foundational theorems about sets; always true, never disabled.            *)
SetExtensionality == "SetExtensionality"
PowerSetNotUniversal == "PowerSetNotUniversal"

SPECIFICATION == DispatchZenon
INIT == DispatchZenon
NEXT == DispatchZenon
INVARIANTS == DispatchZenon
PROPERTIES == DispatchZenon

====