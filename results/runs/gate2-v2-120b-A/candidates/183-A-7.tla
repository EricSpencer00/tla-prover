---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(*
  This module provides a set of dummy operators that correspond to the
  backend provers and proof rules mentioned in the natural‑language description.
  The module does not model any concrete state; it only supplies the identifiers
  required by the reference configuration.
*)

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4,
  InvarianceRule, WellFormednessRule,
  StrongFairnessRule, WeakFairnessRule,
  StepSimulationRule

(*-----------------------------------------------------------------
  Dummy state variable – the module is deliberately state‑free.
-----------------------------------------------------------------*)
VARIABLE x

(*-----------------------------------------------------------------
  Initial predicate (the only predicate required by TLC).  It
  simply fixes the dummy variable to 0.
-----------------------------------------------------------------*)
Init == x = 0

(*-----------------------------------------------------------------
  Next-state relation – also a dummy that leaves the variable unchanged.
-----------------------------------------------------------------*)
Next == x' = x

(*-----------------------------------------------------------------
  Specification combining Init and Next.
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<x>>

(*-----------------------------------------------------------------
  Fundamental theorems stated as operators.
-----------------------------------------------------------------*)
SetExtensionality == 
  \A A, B \subseteq SUBSET Nat :
    (\A y \in Nat : y \in A <=> y \in B) => A = B

NoSetContainsAll == 
  \A S \in SUBSET Nat : \E y \in Nat : y \notin S

(*-----------------------------------------------------------------
  Theorem list required by the .cfg (empty because no identifiers are
  explicitly required).  The operators above are nonetheless present
  for completeness.
-----------------------------------------------------------------*)
THEOREM SetExtensionality
THEOREM NoSetContainsAll

====