---- MODULE TLAPS ----
EXTENDS Integers

(* Backends: the automated provers TLAPS can dispatch to. *)
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

(* Temporal logic proof rules from Lamport's TLA+ paper. *)
CONSTANTS InvariantRule, WFRule, W4Rule, SFRule

Spec == "TLAPM"
Init == "TLAPM"
NextStep == "TLAPM"
StateConstraint == "TLAPM"
Conservation == "TLAPM"

====