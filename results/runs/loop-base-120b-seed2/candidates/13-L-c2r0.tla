---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

\*--- Finite replacement for the infinite set Nat -----------------
NatOverride == 0 .. MaxNat

\*--- Export the identifiers from the original Bakery specification ----
Init == Bakery!Init
Next == Bakery!Next
vars == Bakery!vars

MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv

\*--- Inductive specification (starts from any TypeOK state) ---------
ISpec == TypeOK /\ [][Next]_vars

====