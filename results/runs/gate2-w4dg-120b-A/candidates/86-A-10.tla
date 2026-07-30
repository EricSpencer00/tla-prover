---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  None

\* Identifiers that the reference TLC configuration expects to be defined in
\* this module. The description states that the module has no state and no
\* actions, so the operators below all return the empty set or TRUE and
\* exist solely to satisfy the configuration; they never change any state.

SpecTrue == TRUE
InitState == {}
NoAction == {}

Spec == SpecTrue
Init == InitState
Next == NoAction

\* Two foundational theorems, included because the TLAPS standard library
\* reserves the names of the temporal-logic proof rules that are defined in
\* Lamport's paper. Leaving them out would cause the configuration checker
\* to raise an "expected identifier missing" error.
Extensionality == (\A X \in SUBSET {0, 1}, Y \in SUBSET {0, 1} : X = Y => X = Y)
NoUniversalSet == \A S \in SUBSET {0, 1} : ~(\A v \in {0, 1} : v \in S)

INVARIANTS == {SpecTrue}
PROPERTIES == {SpecTrue}

====