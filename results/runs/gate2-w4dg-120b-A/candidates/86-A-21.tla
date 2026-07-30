---- MODULE TLAPS ----
\* Backend provers for the TLA Proof System, plus core temporal-logic proof rules.
EXTENDS Naturals

CONSTANTS
  \* No actors or state in this module; the constants are "vacuous slots"
  \* that the reference configuration expects to exist.
  NOT_SPECIFIED

\* The spec is a conjunction of the standard structural operators; the module
\* carries no substantive state, so the operators below are all stubs.
SPECIFICATION == Init /\ Next

Init == TRUE
Next == TRUE

\* Reserved for the two foundational set-theory theorems.
INVARIANTS == Extensionality /\ UniversalityNotSet

\* No progress property is required in this module.
PROPERTIES == TRUE

\* No substantive state, so there is nothing to evacuate.
EVACUATE == TRUE

\* The invariant that two sets with the same elements are equal.
Extensionality == \A X \in SUBSET UNIV, Y \in SUBSET UNIV :
  (\A z \in UNIV : (z \in X) <=> (z \in Y)) => X = Y

\* No set contains every possible value.
UniversalityNotSet == \A X \in SUBSET UNIV : X # UNIV

\* Temporal logic proof rules (included as reserved names, taken from Lamport's
\* TLA paper). They carry no proof steps here, only the identifiers.
\* Invariance rule: if a step keeps a property true, and it starts true, it stays.
Invariance == TRUE
WellFormed == TRUE
StrongFairness == TRUE
WeakFairness == TRUE
NextSimulation == TRUE

\* Backend provers, invoked by the proof system via these identifiers.
Zeno == TRUE
Isabelle == TRUE
CVC3 == TRUE
Yices == TRUE
VeriT == TRUE
Z3 == TRUE
SPASS == TRUE
LS4 == TRUE

====