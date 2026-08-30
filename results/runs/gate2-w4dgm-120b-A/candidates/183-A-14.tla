---- MODULE TLAPS ----
EXTENDS Naturals

(* Backend provers and solvers for the TLA+ Proof System.                      *)
(* These operators are not executed here; they name the provers TLAPS may     *)
(* invoke.  The two theorems below are the only logical claims this module   *)
(* makes.  The fairness and invariance rules mentioned in the description are  *)
(* from Lamport's paper and are reserved names in the library.                *)

\* Dispatch a proof obligation to the Zenon first-order theorem prover.
Zenon == "zenon"

\* Dispatch a proof obligation to Isabelle/HOL via Sledgehammer.
Isabelle == "smtIsa"

\* Dispatch a proof obligation to the CVC3 SMT solver.
CVC3 == "cvc3"

\* Dispatch a proof obligation to the Yices SMT solver.
Yices == "yices"

\* Dispatch a proof obligation to the veriT SMT solver.
Verit == "verit"

\* Dispatch a proof obligation to the Z3 SMT solver.
Z3 == "z3"

\* Dispatch a proof obligation to the SPASS theorem prover.
SPASS == "spass"

\* Dispatch a proof obligation to LS4, the LTL prover.
LS4 == "ls4"

(* Set extensionality: two sets with the same elements are equal.            *)
Extensionality ==
  \A X, Y \in SUBSET Nat :

    (\A x \in Nat : (x \in X) <=> (x \in Y)) => (X = Y)

(* No set contains every natural number.                                     *)
NotUniversal ==
  \A X \in SUBSET Nat :

    (~ (\A x \in Nat : x \in X))
====