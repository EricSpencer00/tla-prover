---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\*  Finite version of the natural numbers set, used to override the
\*  infinite Nat in the model-checking configuration.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\*  State predicates and actions inherited from the original Bakery spec.
\* ----------------------------------------------------------------------
INIT == Bakery!Init
NEXT == Bakery!Next

\* ----------------------------------------------------------------------
\*  Invariants inherited from the original Bakery spec.
\* ----------------------------------------------------------------------
MutualExclusion == Bakery!MutualExclusion
TypeOK           == Bakery!TypeOK
Inv              == Bakery!Inv

\* ----------------------------------------------------------------------
\*  Collections required by the TLC configuration.
\* ----------------------------------------------------------------------
INVARIANTS == { MutualExclusion, TypeOK, Inv }
PROPERTIES == {}

\* ----------------------------------------------------------------------
\*  Inductive specification: start from any type‑correct state satisfying
\*  the invariant rather than only the initial state.
\* ----------------------------------------------------------------------
ISpec == TypeOK /\ [][NEXT]_vars

====