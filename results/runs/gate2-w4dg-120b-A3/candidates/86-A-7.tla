---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  z3Turbo

\* Backend pragmas for TLAPS: dispatch proof obligations to automated theorem
\* provers and SMT solvers (Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS,
\* LS4).
Pragmas == {
  [solver |-> "zenon"],
  [solver |-> "isabelle"],
  [solver |-> "cvc3"],
  [solver |-> "yices"],
  [solver |-> "verit"],
  [solver |-> "z3", tactic |-> "smt", param |-> z3Turbo],
  [solver |-> "spass"],
  [solver |-> "ls4"]
}

\* Temporal logic proof rules, quoted from Lamport's "The Temporal Logic of
\* Actions": invariance, well-formedness, strong fairness, weak fairness,
\* and step simulation. They are included here as reserved names.
Invariance == TRUE
Step == [type |-> "step"]
BStep == [type |-> "bstep"]
Stutter == [type |-> "stutter"]
Recur == [type |-> "recur"]
SpecStep == [type |-> "specstep"]
WF == TRUE
SF == TRUE

\* Two foundational theorems: set extensionality and that no set contains
\* every possible value.
SetExtensionality == TRUE
NoSetContainsAll == TRUE

\* The specification is deliberately trivial: it only folds the above
\* declarations into the shape the .cfg expects, with no real state or
\* transition.
Specification == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====