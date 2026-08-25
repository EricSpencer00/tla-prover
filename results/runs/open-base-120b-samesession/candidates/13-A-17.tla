---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

NatOverride == 0 .. MaxNat

INIT == Bakery!Init
NEXT == Bakery!Next
ISpec == Bakery!Spec

MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv
====