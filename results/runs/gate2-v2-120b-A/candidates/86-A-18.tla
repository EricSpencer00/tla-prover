---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(*  TLAPS Backend Configuration and Fundamental Temporal Logic Rules      *)
(*  This module defines backend pragmas for TLAPS and reserves names for   *)
(*  basic temporal logic proof rules. No state variables are introduced.   *)
(***************************************************************************)

(***************************************************************************)
(*  Backend prover configuration operators                                *)
(*  These operators do not affect the model's behavior; they are only    *)
(*  placeholders so that TLAPS recognises the provers and associated     *)
(*  parameters.                                                          *)
(***************************************************************************)

(* Zenon prover with a 30‑second timeout *)
Zenon == "timeout=30s"

(* Isabelle/HOL prover *)
Isabelle == "default"

(* CVC3 SMT solver *)
CVC3 == "default"

(* Yices SMT solver *)
Yices == "default"

(* veriT prover *)
VeriT == "default"

(* Z3 SMT solver *)
Z3 == "default"

(* SPASS prover *)
SPASS == "default"

(* LS4 temporal logic prover *)
LS4 == "default"

(***************************************************************************)
(*  Reserved names for temporal logic proof rules (no implementation)    *)
(***************************************************************************)

InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

(***************************************************************************)
(*  Fundamental theorems about sets                                      *)
(***************************************************************************)

SetExtensionality == \A x \in UNIV : (x \in S) = (x \in T) => S = T

NoSetIsUniversal == \A S \in SUBSET UNIV : \E x \in UNIV : x \notin S

(***************************************************************************)
(*  Specification placeholders                                            *)
(***************************************************************************)

(* No state variables are defined; the spec is therefore trivial. *)

SPECIFICATION == TRUE
INIT == TRUE
NEXT == UNCHANGED << >>
INVARIANTS == SetExtensionality
PROPERTIES == NoSetIsUniversal

=============================================================================