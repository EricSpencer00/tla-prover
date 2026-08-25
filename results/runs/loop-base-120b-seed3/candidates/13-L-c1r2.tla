---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

\* ----------------------------------------------------------------------
\* Finite version of Nat for model checking (overrides the infinite Nat)
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* Specification and invariant aliases required by the .cfg file
\* ----------------------------------------------------------------------
ISpec == Spec                \* inductive specification (from Bakery)

MutualExclusion == Bakery!MutualExclusion
TypeOK          == Bakery!TypeOK
Inv             == Bakery!Inv

====