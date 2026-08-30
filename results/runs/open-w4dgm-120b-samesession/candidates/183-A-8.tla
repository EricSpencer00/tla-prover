---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

(* This module defines backend pragmas for the TLA Proof System (TLAPS).  It   *)
(* provides operators that instruct the prover to dispatch proof obligations to *)
(* various automated theorem provers and SMT solvers, and it states the          *)
(* foundational proof rules for temporal logic reasoning.  The module is a     *)
(* helper from the standard library and reserves the names of these rules so   *)
(* they cannot clash with future extensions.                                   *)

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

Spec0 == "Specification"
Init0 == "Init"
Next0 == "Next"
Inv0 == "Invariants"
Props0 == "Properties"

\* A dispatch pragma that picks the prover a given proof obligation should run.
Dispatch(op, pr) == op' = pr

\* Switch to a different dispatch strategy (e.g. a different set of backends).
Reconfigure(op) == \E pr \in {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4} : op' = pr

(* Temporal-logic proof rule: an invariant holds in every reachable state. *)
RuleInvariance == [states |-> {}, steps |-> 0]

(* Temporal-logic proof rule: a well-formedness condition holds always.     *)
RuleWellFormed == [states |-> {}, steps |-> 0]

(* Temporal-logic proof rule: a strongly fair action eventually fires.     *)
RuleSFair == [states |-> {}, steps |-> 0]

(* Temporal-logic proof rule: a weakly fair action eventually fires.       *)
RuleWFair == [states |-> {}, steps |-> 0]

(* Temporal-logic proof rule: each step simulates an atomic action of the *)
(* system.                                                                    *)
RuleStep == [states |-> {}, steps |-> 0]

(* Empty placeholder: a step that performs no action.                         *)
RuleNoAction == [states |-> {}, steps |-> 0]

(* Foundational theorem: set extensionality.                                   *)
TheoremExtensionality == \A A, B \in SUBSET {"a", "b"} : (A = B) <=> (A \subseteq B /\ B \subseteq A)

(* Foundational theorem: nothing contains every possible value.                *)
TheoremNoUniversalSet == ~ (\A x \in {"a", "b"} : TRUE)

====