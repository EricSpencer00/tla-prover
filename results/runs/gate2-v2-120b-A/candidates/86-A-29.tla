---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(***************************************************************************)
(* The TLAPS module provides a collection of backend pragmas and           *)
(* temporal‑logic proof rules used by the TLA+ Proof System (TLAPS).       *)
(* The identifiers defined here are reserved for use by the proof system  *)
(* and for importing the standard proof library.                          *)
(***************************************************************************)

(***************************************************************************)
(* BACKEND PRAGMAS FOR AUTOMATED PROVER DISPATCH                           *)
(***************************************************************************)

\* Dispatch a proof to the Zenon prover.
Zenon == TRUE

\* Dispatch a proof to the Isabelle/HOL prover.
Isabelle == TRUE

\* Dispatch a proof to the CVC3 SMT solver.
CVC3 == TRUE

\* Dispatch a proof to the Yices SMT solver.
Yices == TRUE

\* Dispatch a proof to the veriT SMT solver.
VeriT == TRUE

\* Dispatch a proof to the Z3 SMT solver.
Z3 == TRUE

\* Dispatch a proof to the SPASS theorem prover.
SPASS == TRUE

\* Dispatch a proof to the LS4 temporal‑logic prover.
LS4 == TRUE

(***************************************************************************)
(* TEMPORAL‑LOGIC PROOF RULES (place‑holders)                               *)
(* These operators are defined as TRUE constants to reserve the names.   *)
(***************************************************************************)

\* Invariance rule.
InvRule == TRUE

\* Well‑formedness rule.
WFRule == TRUE

\* Strong fairness rule.
SFRule == TRUE

\* Weak fairness rule.
WFairnessRule == TRUE

\* Step‑simulation rule.
StepSimRule == TRUE

(***************************************************************************)
(* BASIC SET‑THEORY THEOREMS (as theorems, not just operators)             *)
(***************************************************************************)

\* Set extensionality: two sets with the same elements are equal.
SetExtensionality == 
  \A A, B \in SUBSET Nat :
    (\A x : x \in A <=> x \in B) => A = B

\* There is no universal set that contains every possible value.
NoUniversalSet == 
  ~(\E U : \A x \in Nat : x \in U)

=============================================================================