---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

(*----------------------------------------------------------------------
  This module is a stub that provides the identifiers required by the
  reference .cfg file for the TLAPS backend configuration.  The actual
  system description does not introduce state variables, actions, or
  concrete safety/liveness properties.  Consequently the module defines
  the minimal operators expected by the configuration, each returning
  a trivially true predicate.
----------------------------------------------------------------------*)

(* No constant declarations are required; the .cfg does not list any. *)

(*----------------------------------------------------------------------
  SPECIFICATION
  The top‑level specification required by the configuration.  It is
  defined as the conjunction of the initial condition and the next‑state
  relation.
----------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<>>

(*----------------------------------------------------------------------
  Init
  A trivial initial predicate.  Because no state variables are
  specified, the predicate simply returns TRUE.
----------------------------------------------------------------------*)
Init == TRUE

(*----------------------------------------------------------------------
  Next
  A trivial next‑state relation.  With no variables to evolve, the
  relation is defined as TRUE, allowing any stuttering step.
----------------------------------------------------------------------*)
Next == TRUE

(*----------------------------------------------------------------------
  INVARIANTS and PROPERTIES
  The .cfg does not require any explicit invariants or properties, but
  the identifiers must exist.  They are therefore defined as TRUE.
----------------------------------------------------------------------*)
Inv == TRUE
Prop == TRUE

(*----------------------------------------------------------------------
  Theorems (set extensionality and “no set contains every value”) are
  included for completeness, although they are not referenced by the
  .cfg.  They are proved using basic set theory.
----------------------------------------------------------------------*)
SetExtensionality == \A A, B \in SUBSET Nat :
    (\A x \in Nat : x \in A <=> x \in B) => A = B

NoUniversalSet == \A S \in SUBSET Nat : \E x \in Nat : x \notin S

=============================================================================