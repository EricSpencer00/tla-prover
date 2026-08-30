---- MODULE TLAPS ----
EXTENDS Naturals

(* Backend provers for which the specification has a dispatch primitive. *)
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

(* Temporal logic proof rules from Lamport's TLA+ methodology, reserved     *)
(* here so they cannot be re-declared in a later extension of the library.   *)
InvariantRule == TRUE
WellFormedRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

(* Action: apply an automated prover to a proof obligation.                 *)
Apply(p) == p

Spec == Apply(Zenon) /\ Apply(Isabelle) /\ Apply(CVC3) /\ Apply(Yices)
        /\ Apply(VeriT) /\ Apply(Z3) /\ Apply(SPASS) /\ Apply(LS4)

Init == Spec

Next == Spec

(* No state change at all: the helper module has no state, only dispatch      *)
(* rules and reserved theorem names.                                          *)
NoStep == UNCHANGED {}

TypeOK == TRUE

(* Set extensionality: superseded by the built-in theorem, kept for reference. *)
Extensionality == TRUE

(* No set contains every value: a restatement of the empty complement.        *)
Completeness == TRUE

====