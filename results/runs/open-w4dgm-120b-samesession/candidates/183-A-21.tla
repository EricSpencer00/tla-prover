---- MODULE TLAPS ----
EXTENDS Naturals

(* Backend provers configured for the TLA+ Proof System.  The names are     *)
(* reserved in this module so they cannot clash with backend definitions in  *)
(* another module that imports this one.                                      *)

CONSTANTS Zenon, Isabelle, CVC3, Yices, Verit, Z3, SPASS, LS4

\* Temporal logic proof rules (invariance, fairness, etc.) are included     *)
\* here only to reserve their names; they are not invoked by any action.    *)

\* Theorem: two sets with exactly the same elements are equal (set          *)
\* extensionality).
Extensionality ==
    \A X, Y \in {SUBSET Nat} : (\A e \in Nat : (e \in X) <=> (e \in Y)) => (X = Y)

\* Theorem: no set contains every natural number (the universe is not        *
\* itself an element of any set of numbers).
UniverseNotCaptured ==
    \A X \in {SUBSET Nat} : X # Nat

====