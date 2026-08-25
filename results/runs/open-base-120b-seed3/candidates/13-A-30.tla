---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

\*--- Finite override for Nat ---------------------------------
NatOverride == 0 .. MaxNat

\*--- Inductive specification ---------------------------------
ISpec == /\ TypeOK
        /\ Inv
        /\ [][Next]_vars

====