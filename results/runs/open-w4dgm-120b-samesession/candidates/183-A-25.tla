---- MODULE TLAPS ----
EXTENDS Naturals

(* Backend provers/solvers that TLAPS can dispatch to, and the theorem-       *)
(* proving rules it assumes from Lamport's TLA+ paper.                         *)
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

(* Dispatch a proof obligation to a selected backend prover.                  *)
Dispatch(p) == p

(* Temporal logic proof rules (kept as names here to reserve them for the     *)
(* proof system; they do not change state).                                    *)
Invariance == TRUE
WellFormedness == TRUE
StrongFairness == TRUE
WeakFairness == TRUE
StepSimulation == TRUE

(* Foundational theorems assumed by the proof system.                         *)
SetExtensionality == TRUE
NoUniversalSet == TRUE

(* The module configures the backends and reserves the rule names; it does    *)
(* not itself track any proof state.                                          *)
Spec == UNCHANGED

Init == UNCHANGED

Next == UNCHANGED

TypeOK == TRUE

SpecOK == Spec

====