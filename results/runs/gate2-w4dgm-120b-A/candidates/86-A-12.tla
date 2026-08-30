---- MODULE TLAPS ----
EXTENDS Naturals

(* Operators that name the automated provers and solvers TLAPS dispatches to. *)
Zenon      == "zenon"
Isabelle   == "isabelle"
CVC3       == "cvc3"
Yices      == "yices"
VeriT      == "verit"
Z3         == "z3"
SPASS      == "spass"
LS4        == "ls4"

(* Temporal-logic proof rules from Lamport's TLA+ correctness arguments.    *)
(* The rules themselves are not applied here; they are named to reserve   *)
(* their symbols for future proof steps, keeping the shared library clash- *)
(* free as it evolves alongside the system being verified.                *)

Conserves == \A S, T \in SUBSET Nat : (S = T) => (\A x \in S : x \in T)
Nondescends == \A f \in [Nat -> Nat] : (\A i \in Nat : f[i + 1] >= f[i])

SPEC        == TRUE
INIT        == TRUE
NEXT        == TRUE
INVARIANTS  == {Conserves}
PROPERTIES  == {Nondescends}
====