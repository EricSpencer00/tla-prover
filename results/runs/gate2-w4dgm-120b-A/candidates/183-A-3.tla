------------------------ MODULE TLAPS ------------------------
EXTENDS Naturals

(* Backend provers for the TLA Proof System and fundamental temporal-logic *)
(* proof rules.  These operators are configuration hooks for TLAPS.  The   *)
(* set-theoretic theorems are included as the module's foundational        *)
(* invariants.  No system state is modeled here.                           *)

CONSTANTS Operators

(* Dispatch a proof obligation to an automated theorem prover or SMT solver. *)
Dispatch(op) == op \in Operators

(* Fundamental temporal-logic proof rules (reserved names from Lamport's TLA+ *)
(* paper, included here so they cannot be redefined elsewhere).            *)
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

(* Set extensionality: two sets with the same elements are equal.          *)
Extensionality == \A A, B \in SUBSET Operators : (A = B) <=> (\A x \in Operators : (x \in A) <=> (x \in B))

(* No set contains every possible value: no subset of the operators is    *)
(* equal to the entire operator set.                                      *)
NoTotalSet == \A A \in SUBSET Operators : A # Operators

Init == TRUE
Next == TRUE

SPECIFICATION == Init /\ Next
INVARIANTS == Extensionality
PROPERTIES == NoTotalSet
===============================================================