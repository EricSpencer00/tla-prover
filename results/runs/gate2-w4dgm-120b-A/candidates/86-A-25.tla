---- MODULE TLAPS ----
EXTENDS Integers

(* Pragmas that tell TLAPS which backends to invoke for each obligation. *)
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

(* Temporal-logic proof rules, reproduced here for name reservation under the
   standard library.  They are never applied by this module itself. *)
CONSTANTS InvR, WfR, W4R, W3R, SFairR, WFairR

Spec == "Spec"
Init == "Init"
Next == "Next"
Invariants == "Invariants"
Properties == "Properties"

(* Set extensionality: two sets with the same elements are equal. *)
Extensionality ==
    \A X, Y \in SUBSET Int : (\A x \in Int : (x \in X) <=> (x \in Y)) => X = Y

(* No set contains every possible value. *)
NotUniversal ==
    \A S \in SUBSET Int : S # Int

====