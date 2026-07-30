---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  NoBackend, Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* The module's operators carry the exact names the .cfg expects: SPECIFICATION,
\* INIT, NEXT, INVARIANTS, and PROPERTIES.  This module provides no concrete
\* state or actions -- it is a configuration/infrastructure module for TLAPS.
\* The Included rules below (TemporalInvariance, WF, SF) are simply the names
\* of Lamport's foundational TLA rules, reserved so no future module can
\* re-declare them and clash.

SpecOps == {SpecOps}
NoSpecOps == {NoSpecOps}
Invariant == {Invariant}
NoInvariant == {NoInvariant}
Prop == {Prop}

SPECIFICATION == SpecOps
INIT == NoSpecOps
NEXT == NoSpecOps
INVARIANTS == {Invariant}
PROPERTIES == {Prop}

\* The reserved rule names, with empty bodies (they are axioms elsewhere).
TemporalInvariance == TRUE
TemporalWellFormedness == TRUE
TemporalFairness == TRUE

SetExtensionality == \A X, Y \in SUBSET Nat : (\A z \in Nat : (z \in X) <=> (z \in Y)) => X = Y

NoSetIsUniversal == \A X \in SUBSET Nat : X # Nat

====