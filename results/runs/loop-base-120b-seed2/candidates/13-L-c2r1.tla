---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT MaxNat

\*--- Finite replacement for the infinite set Nat -----------------
NatOverride == 0 .. MaxNat

\*--- Inductive specification (starts from any TypeOK state) ---------
ISpec == TypeOK /\ [][Next]_vars

====