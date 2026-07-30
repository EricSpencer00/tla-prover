---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

ASSUME Zenon = "Zenon"
ASSUME Isabelle = "Isabelle"
ASSUME CVC3 = "CVC3"
ASSUME Yices = "Yices"
ASSUME veriT = "veriT"
ASSUME Z3 = "Z3"
ASSUME SPASS = "SPASS"
ASSUME LS4 = "LS4"

\* No state, no actors: this module only configures the TLAPS backends and
\* reserves the names of the temporal logic proof rules (the invariance rule,
\* the well-formedness rule, and both the weak and strong fairness rules).

SpecStatement ==
  "The set-extensionality theorem and the no-universal-set theorem are the only
   theorems about sets that this module provides."

InvarianceRule ==
  "An invariant maintains truth across every reachable state."

WellFormednessRule ==
  "A well-formed action respects the typing of every variable it touches."

WeakFairnessRule ==
  "If an action is continuously enabled, it eventually occurs."

StrongFairnessRule ==
  "If an action is enabled infinitely often, it eventually occurs."

SPECIFICATION == SpecStatement
INIT == UNCHANGED {}
NEXT == UNCHANGED {}
INVARIANTS == InvarianceRule
PROPERTIES == WellFormednessRule
LIVENESS == WeakFairnessRule
\* The fairness rule below is the second liveness property the spec reserves.
FUTURE == StrongFairnessRule

====