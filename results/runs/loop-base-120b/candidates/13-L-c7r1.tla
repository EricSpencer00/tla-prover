---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANT N, MaxNat

\* Finite override for the infinite set Nat
NatOverride == 0 .. MaxNat

\* Instantiate the original Bakery specification, overriding Nat with NatOverride
INSTANCE Bakery AS B WITH N <- N, Nat <- NatOverride

\* Set of variables used by the instance (the tuple of all state variables)
Vars == <<B!pc, B!flag, B!ticket>>

\* Inductive specification (starts from any type‑correct state)
ISpec == B!TypeOK /\ [][B!Next]_Vars

\* Invariants (re‑exposed from the instance)
MutualExclusion == B!MutualExclusion
TypeOK == B!TypeOK
Inv == B!Inv
====