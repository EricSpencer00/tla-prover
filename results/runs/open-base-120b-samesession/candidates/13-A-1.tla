---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* Include the original Bakery specification
INSTANCE Bakery

\* Invariants required by the configuration
MutualExclusion == Bakery!MutualExclusion
TypeOK          == Bakery!TypeOK
Inv             == Bakery!Inv

\* Inductive specification: start from any type‑correct state satisfying the invariant
ISpec == (TypeOK /\ Inv) /\ [][Bakery!Next]_<<Bakery!pc, Bakery!ticket, Bakery!choosing>>

====