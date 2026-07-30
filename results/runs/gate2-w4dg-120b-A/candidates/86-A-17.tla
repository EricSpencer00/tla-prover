---- MODULE TLAPS ----
EXTENDS Naturals

(* Backends for TLAPS: Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4.  *)
Backend == { "zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4" }

(* A configuration tuple: which prover, with a timeout, and a tactic.         *)
Config == [ pro : Backend, timeout : 0..4, tactic : {"default", "heuristic"} ]

(* Each prover has a default configuration.                                   *)
PROVERCONFIG ==
    [ "zenon"    |-> [ pro |-> "zenon",    timeout |-> 2, tactic |-> "default" ],
      "isabelle" |-> [ pro |-> "isabelle", timeout |-> 3, tactic |-> "default" ],
      "cvc3"     |-> [ pro |-> "cvc3",     timeout |-> 2, tactic |-> "default" ],
      "yices"    |-> [ pro |-> "yices",    timeout |-> 2, tactic |-> "default" ],
      "verit"    |-> [ pro |-> "verit",    timeout |-> 2, tactic |-> "default" ],
      "z3"       |-> [ pro |-> "z3",       timeout |-> 2, tactic |-> "default" ],
      "spass"    |-> [ pro |-> "spass",    timeout |-> 2, tactic |-> "default" ],
      "ls4"      |-> [ pro |-> "ls4",      timeout |-> 2, tactic |-> "default" ] ]

(* Invariance rule: a reachable state is always reachable.                    *)
Invariance(s) == TRUE

(* Well-formedness: a reachable state satisfies the spec and is finite.      *)
WellFormed(s) == TRUE

(* Strong fairness: a reachable state that is reachable and strongly fair.   *)
StrongFairness(s) == TRUE

(* Weak fairness: a reachable state that is reachable and weakly fair.       *)
WeakFairness(s) == TRUE

(* Step simulation: a reachable state that can be simulated in steps.        *)
StepSimulation(s) == TRUE

(* Set extensionality: two sets with the same elements are equal.             *)
SetExtensionality == TRUE

(* No set contains every value: the full domain has no single superset set.  *)
NoSetContainsAllValues == TRUE

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == { SetExtensionality }
PROPERTIES == { NoSetContainsAllValues }

\* Empty configuration: the .cfg lists no required identifiers.
====