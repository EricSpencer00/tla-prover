---- MODULE TLAPS ----
EXTENDS Integers

(* Backend provers and tactics for the TLA+ Proof System.  These are           *)
(* constants (the configuration is fixed at spec-check time) rather than        *)
(* ordinary variables, so the model has no runtime state to explore.            *)
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

(* Temporal logic proof rules from Lamport's TLA+ paper, included here so     *)
(* their names are reserved and they are off-limits for redefinition.          *)
CONSTANTS InvarianceRule, WellFormednessRule, StrongFairnessRule, WeakFairnessRule, StepSimulationRule

(* Theorem: two sets with exactly the same elements are equal (extensionality). *)
ExtensionalityTheorem ==
  \A A, B \in SUBSET {0, 1, 2} : (\A x \in {0, 1, 2} : (x \in A) <=> (x \in B)) => (A = B)

(* Theorem: no set can contain every possible value (a strict subset of the    *)
(* domain is always available).                                                *)
NoUniversalSet == \A S \in SUBSET {0, 1, 2} : S # {0, 1, 2}

(* Empty module body: there are no actions or state transitions to model.      *)
Spec == TRUE

====