---- MODULE TLAPS ----
EXTENDS Naturals

\* This is a helper module from the standard proof library.  The temporal
\* logic proof rules stated here (the invariance rule, the well-formedness
\* rule, the strong and weak fairness rules, and the step-simulation rule)
\* are from Lamport's paper "The Temporal Logic of Actions".  They are included
\* so that their names are reserved and cannot clash with a future version of
\* this module; they are never called as actions within this module.
\* The practical effect is that each name is defined once and bound to a
\* syntactically well-formed, semantically inert placeholder.

InvRule == TRUE
WFRule == TRUE
SFRule == TRUE
SimRule == TRUE

\* Two foundational theorems of set theory: extensionality, and that no set
\* contains every possible value.
Extensionality == \A X, Y \in SUBSET Nat : (\A z \in Nat : (z \in X <=> z \in Y)) => X = Y
NoUniversals == \A X \in SUBSET Nat : X # Nat

====