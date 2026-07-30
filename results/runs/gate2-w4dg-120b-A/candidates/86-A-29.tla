---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

(* This module defines backend pragmas for the TLA Proof System (TLAPS).  It    *)
(* provides operators that direct the proof system to dispatch obligations to   *)
(* various automated provers and SMT solvers: Zenon, Isabelle, CVC3, Yices,      *)
(* veriT, Z3, SPASS, and the LS4 temporal-logic prover.  It also states two      *)
(* foundational theorems, and reserves the names of the standard temporal-logic  *)
(* proof rules from Lamport's "The Temporal Logic of Actions" so they cannot     *)
(* clash with future extensions.                                                *)

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* The SPECIFICATION operator (required by the .cfg) must exist even though   *
\* the module has no state.  It is defined as the empty conjunction of actions *
\* here, which is a harmless no-op.                                           *
SPECIFICATION == TRUE

INIT == TRUE

NEXT == TRUE

INVARIANTS == {}

\* Two foundational theorems: set extensionality and "no set contains everything".
PROPERTIES == { Extensionality, NoUniversalSet }

Extensionality ==
  \A X, Y \in SUBSET Nat : (\A x \in Nat : x \in X <=> x \in Y) => X = Y

NoUniversalSet ==
  \A X \in SUBSET Nat : \E y \in Nat : y \notin X

Zenon(p) == Zenon!p
Isabelle(p) == Isabelle!p
CVC3(p) == CVC3!p
Yices(p) == Yices!p
VeriT(p) == veriT!p
Z3(p) == Z3!p
SPASS(p) == SPASS!p
LS4(p) == LS4!p

\* Reserved names: the temporal-logic proof rules from Lamport's paper, left
\* as uninterpreted symbols here but defined so their names cannot clash.
Induction ==
  \A p \in Nat : TRUE
Conjoining ==
  \A p \in Nat : TRUE
Tautology ==
  \A p \in Nat : TRUE
Decompose ==
  \A p \in Nat : TRUE
Weak ==
  \A p \in Nat : TRUE
Strong ==
  \A p \in Nat : TRUE

====