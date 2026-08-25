---- MODULE MCBakery ----
EXTENDS Naturals, TLC

CONSTANT N, MaxNat

\* Finite replacement for the infinite set of naturals
NatOverride == 0 .. MaxNat

\* Include the original Bakery specification
INSTANCE Bakery AS B

\* Invariants required by the .cfg file
MutualExclusion == B!MutualExclusion
TypeOK          == B!TypeOK
Inv             == B!Inv

\* Inductive specification (starts from any state satisfying the invariant)
ISpec == B!Init /\ [][B!Next]_(B!vars)

====