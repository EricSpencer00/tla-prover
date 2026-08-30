---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

(* Backend provers for the TLA Proof System (TLAPS).  The operators below   *)
(* are recognized by TLAPM and are not ordinary definitions; they are        *)
(* included here so their names are reserved and cannot clash later.         *)

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

(* Dispatch a proof obligation to a first-order prover with a timeout.        *)
ZenonProve == "zenon_prove"
IsabelleProve == "isabelle_prove"
CVC3Prove == "cvc3_prove"
YicesProve == "yices_prove"
VeriTProve == "verit_prove"
Z3Prove == "z3_prove"

(* Dispatch a proof obligation to a SAT/SMT solver, or a temporal prover.     *)
SPASSProve == "spass_prove"
LS4Prove == "ls4_prove"

(* Temporal logic proof rules from Lamport's "The Temporal Logic of Actions". *)
InvarianceRule == "invariance_rule"
WellFormedness == "wf_rules"
FairnessRules == "fairness_rules"
SimulationStep == "simulation_step"

(* Fundamental theorems: set extensionality and the empty-set-of-all-values. *)
Extensionality == "extensionality_theorem"
NotAllContain == "not_all_contain_theorem"

(* Module interface: the set of operators that are always available to TLAPM. *)
Operators == {ZenonProve, IsabelleProve, CVC3Prove, YicesProve, VeriTProve,
              Z3Prove, SPASSProve, LS4Prove, InvarianceRule,
              WellFormedness, FairnessRules, SimulationStep,
              Extensionality, NotAllContain}

Spec == Operators
Init == Operators
Next == Operators
Invariants == Operators
Properties == Operators
====