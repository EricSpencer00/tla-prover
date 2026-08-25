---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

\* Tuple of state variables (as defined in the Bakery module)
Vars == <<pc, ticket>>

\* Inductive specification: start from any type‑correct state satisfying the invariant
ISpec == TypeOK /\ [][Bakery!Next]_Vars

\* Invariants (aliases to the definitions in the Bakery module)
MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv

====