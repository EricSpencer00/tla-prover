---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(*  Backend pragma operators for TLAPS                                      *)
(*  These are declared as nullary operators that represent directives to   *)
(*  the TLA proof system.  They do not affect the executable semantics of  *)
(*  the specification; they are only used by TLAPS when the spec is       *)
(*  processed by the prover.                                               *)
(***************************************************************************)

\* Dispatch proof obligations to various automated provers/SMT solvers
Zenon      == "Zenon"
Isabelle   == "Isabelle"
CVC3       == "CVC3"
Yices      == "Yices"
VeriT      == "VeriT"
Z3         == "Z3"
SPASS      == "SPASS"
LS4        == "LS4"

\* Time‑out and tactic directives (represented as plain constants)
ZenonTimeout   == 30      \* seconds
IsabelleTimeout== 60
SMTTimeout     == 60
Verification   == "default"

(***************************************************************************)
(*  Temporal‑logic proof rule names (reserved for future use)              *)
(***************************************************************************)

WellFormed        == "WellFormed"
Invariance        == "Invariance"
StrongFairness    == "StrongFairness"
WeakFairness      == "WeakFairness"
StepSimulation    == "StepSimulation"

(***************************************************************************)
(*  Since the module only supplies configuration information, the           *)
(*  operational part of the spec is the trivial identity system.           *)
(*  We therefore define a single state variable that never changes.       *)
(***************************************************************************)

VARIABLES dummy

Init == dummy = 0

Next == UNCHANGED dummy

(***************************************************************************)
(*  Safety theorems required by the description                           *)
(***************************************************************************)

SetExtensionality ==
  ASSUME \A S, T \in SUBSET UNIV :
          (\A x \in UNIV : x \in S <=> x \in T) => S = T

NoSetContainsAllValues ==
  ASSUME \A S \in SUBSET UNIV : \E x \in UNIV : x \notin S

=============================================================================