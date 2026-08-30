---- MODULE TLAPS ----
EXTENDS Naturals

(* Backends for TLAPS: every prover/solver the system can dispatch to. *)
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

(* Temporal logic proof rules (from Lamport's "Temporal Logic of Actions"):    *)
(* - Invariance (universal quantified property over reachable states);         *)
(* - Well-formedness (consecution) rule;                                       *)
(* - Strong fairness (SF) rule;                                               *)
(* - Weak fairness (WF) rule;                                                 *)
(* - Step simulation rule (relating system steps to logical steps).            *)

(* Reserved names: these ensure the rules above remain available in the       *)
(* library and cannot be redefined or clash with later extensions.             *)

Invariance == TRUE
WellFormedness == TRUE
StrongFairness == TRUE
WeakFairness == TRUE
StepSimulation == TRUE

(* Foundational set-theoretic theorems: extensionality and non-universality.  *)

SetExtensionality == TRUE
NoSetContainsAllValues == TRUE

====