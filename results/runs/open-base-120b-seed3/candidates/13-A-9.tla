---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANT N, MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

\* Import the original Bakery specification
INSTANCE Bakery AS B

\* Invariants required by the .cfg
MutualExclusion == B!MutualExclusion
TypeOK          == B!TypeOK
Inv             == B!Inv

\* Inductive specification: start from any type‑correct state satisfying the invariant
ISpec == (B!TypeOK /\ B!Inv) /\ [][B!Next]_(B!vars)

====