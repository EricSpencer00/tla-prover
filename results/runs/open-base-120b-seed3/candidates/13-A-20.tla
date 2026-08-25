---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

\* ----------------------------------------------------------------------
\* Finite replacement for the infinite set Nat (used by the .cfg file)
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* Re‑export of the Bakery specification's core operators
\* ----------------------------------------------------------------------
INIT == Bakery!Init
NEXT == Bakery!Next

MutualExclusion == Bakery!MutualExclusion
TypeOK          == Bakery!TypeOK
Inv             == Bakery!Inv

\* ----------------------------------------------------------------------
\* Inductive specification: starts from any state satisfying the invariant
\* ----------------------------------------------------------------------
ISpec == TypeOK /\ Inv /\ [][NEXT]_vars

\* ----------------------------------------------------------------------
\* Collections required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANTS == { MutualExclusion, TypeOK, Inv }
PROPERTIES  == {}

====